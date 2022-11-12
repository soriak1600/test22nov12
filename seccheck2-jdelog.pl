#!/usr/bin/perl

use v5.26.0;
use warnings;

use HTTP::Tiny;
use JSON::PP qw(decode_json);
use List::Util qw(any);
use FindBin qw($Bin);
use File::Spec::Functions qw(abs2rel);
use Cwd qw(realpath);
use Time::HiRes;
use POSIX qw(strftime mktime);
use Getopt::Long;

my $REVIEW_EVERY_MONTHS = 2;

# API key is not a real secret, anyone can obtain one on https://nvd.nist.gov/developers/request-an-api-key
my $API_KEY = '71722391-eb47-474a-9476-214c0be3ecea';
my $DEBUG = 1 if $ENV{DEBUG};
my $ROOT = realpath("$Bin/../../");

# Maps build identifier from build definition to a human-readable build name
# (which is later included into the documentation)

my %BUILD_NAMES = (
    ALL               => 'All',
    aix               => 'AIX',
    aix6              => 'AIX 6',
    'fbsd11-amd64'    => 'FreeBSD 11 x64',
    generic           => 'Generic RPM and DEB',
    'generic-glibc25' => 'Generic GLIBC 2.5',
    macos             => 'MacOS',
    'macos-arm64'     => 'MacOS x64',
    'solaris10-sparc' => 'Solaris 10 SPARC',
    'solaris10-i386'  => 'Solaris 10 i386',
    win64             => 'Windows x64',
);

# Manifest validation schema is pretty self-explaining.
# Types supported are: string, array, hashmap.
# 'match' is a regex. Use qr/./ as 'non-empty' condition.
# For 'array' type with 'match' directive, every element of array is checked against 'match' expression.
# 'schema' defines sub-schema for 'hashmap' and 'array' types.

my $MANIFEST_SCHEMA = {
    name        => { required => 1,                                   type => 'string',              match => qr/./                             },
    cpe23       => {                                                  type => 'string',              match => qr/^cpe:2\.3:[aoh]:[\w-]*:[\w-]+/ },
    type        => { required => 1,                                   type => 'string',              match => qr/^(?:external|embedded)$/       },
    buildSource => { required => sub { $_[0]->{type} eq 'external' }, type => [ 'string', 'array' ], match => qr/^\w+$/                         },
    version     => { required => sub { $_[0]->{type} eq 'embedded' }, type => [ 'string', 'array' ], match => qr/./                             },
    versionMap  => {                                                  type => [ 'string', 'array' ], match => qr/^[\w\.-]+\s*->\s*[\w\.-]+$/    },
    reviewer    => { required => sub { !$_[0]->{cpe23} },             type => 'string',              match => qr/@/                             },
    reviewDate  => { required => sub { !$_[0]->{cpe23} },             type => 'string',              match => qr/^\d{4}-\d\d-\d\d$/             },
    comment     => {                                                  type => 'string'                                                          },
    CVEs        => { type => 'hashmap', keymatch => qr/^CVE-\d{4}-\d{4,}$/, schema => {
	status      => { required => 1, type => 'string', match => qr/^(?:Not\sapplicable|Observed|Active)$/i },
	description => { required => 1, type => 'string', match => qr/./                                      },
	reviewer    => { required => 1, type => 'string', match => qr/@/                                      },
	reviewDate  => { required => 1, type => 'string', match => qr/^\d{4}-\d\d-\d\d$/                      },
	comment     => {                type => 'string'                                                      },

    } }
};

# YAML is the only package used which do not reside in core library

INIT {
    eval 'use YAML';
    if ( $@ ) {
	die <<EOF
YAML package not found. Please install it to be able to run this script as following:

Ubuntu/Debian: # apt install libyaml-perl
RedHat:        # yum install perl-YAML
Arch:          # pacman -Sy perl-yaml
MSYS2:         \$ pacman -Sy perl-YAML
FreeBSD:       # pkg install textproc/p5-YAML

If packaged version is not available on your system, try running as root:

# cpan -i YAML

EOF
    }
}

my $GENDOC;   # Output path if documentation needs to be generated, otherwise undefined
my $PCNT = 0; # Problem counter

my $NOW = strftime('%Y-%m-%d', localtime);


sub logd($) { say STDERR shift if $DEBUG }
sub logp($) { say STDERR "PROBLEM #" . (++$PCNT) . ": $_[0]" }
sub relpath($) { abs2rel(realpath(shift), $ROOT) }

sub usage() {
    say <<EOF
Usage: $0 [ --gendoc <filename> | --help | --usage ]

--gendoc <filename> : Generate a document in AsciiDoc format with the list and
                      description of the vulnerabilities affecting jdelog

--help | --usage    : Show this message and exit
EOF
    ;
    exit 1;
}

GetOptions('gendoc=s' => \$GENDOC, 'help|usage' => \&usage) or usage;

my $builddef_path = "$ROOT/packaging/jdelog_build_definition.yml";
my $builddef = YAML::LoadFile($builddef_path)
    or die "Cannot read build definition $builddef_path\n";

# Hash linking sourceset to an array of builds it is included in
# e.g. oldssl => [ aix, aix6 ]

my %sourceset_to_builds;

push $sourceset_to_builds{ $_->{(keys(%$_))[0]}{sourceSet} }->@*, (keys(%$_))[0]
    for $builddef->{deps}{binary}->@*;

# Hashset linking library identifier (buildSource, in terms of security manifest),
# its version and sourceset
# e.g. $libinfo{openssl10}{1.0.2u}{oldssl} = 1

my %libinfo;

while ( my ( $libid, $ver ) = each $builddef->{deps}{source}{default}->%* )
{
    $ver =~ s/^=//;
    $libinfo{$libid}{$ver}{default} = 1;
}

while ( my ( $sset, $libs ) = each $builddef->{deps}{source}{sets}->%* )
{
    while ( my ( $libid, $ver ) = each %$libs )
    {
	$ver =~ s/^=//;
	$libinfo{$libid}{$ver}{$sset} = 1;
    }
}

# Maps type from validation schema to Perl reference type

my %TYPEMAP = (
    'string'  => '',
    'array'   => 'ARRAY',
    'hashmap' => 'HASH',
);

# Validates a single manifest. Dies on failure. Return value is undefined.

sub validate_manifest($$$);

sub validate_manifest($$$)
{
    my ( $manifest_clause, $manifest, $schema ) = @_;

    for my $k ( keys %$schema )
    {
	my $sch = $schema->{$k};

	die "Required key '$k' is absent in $manifest_clause\n"
	    if !ref $sch->{required} && $sch->{required} && !exists $manifest->{$k} ||
	       ref $sch->{required} eq 'CODE' && $sch->{required}->($manifest) && !exists $manifest->{$k};
    }

    for my $k ( keys %$manifest )
    {
	my $sch = $schema->{$k};
	die "Key '$k' is not known in $manifest_clause\n" unless $sch;

	my %types;

	if ( !ref $sch->{type} )
	{
	    $types{ $TYPEMAP{ $sch->{type} } } = 1;
	}
	elsif ( ref $sch->{type} eq 'ARRAY' )
	{
	    $types{ $TYPEMAP{$_} } = 1 for $sch->{type}->@*;
	}

	die "Value type for key '$k' is not valid in $manifest_clause\n"
	    unless $types{ ref $manifest->{$k} };

	my $validate_scalar = sub
	{
	    my ( $sch, $val ) = @_;
	    die "Value '$val' is not valid for key '$k' in $manifest_clause\n"
		if $sch->{match} && $val !~ $sch->{match};
	};

	if ( !ref $manifest->{$k} )
	{
	    $validate_scalar->( $sch, $manifest->{$k} );
	}
	elsif ( ref $manifest->{$k} eq 'ARRAY' )
	{
	    for ( $manifest->{$k}->@* )
	    {
		if ( $sch->{schema} )
		{
		    validate_manifest($manifest_clause, $_, $sch->{schema} );
		}
		else
		{
		    $validate_scalar->($sch, $_);
		}
	    }
	}
	elsif ( ref $manifest->{$k} eq 'HASH' )
	{
	    while ( my ( $hk, $hv ) = each $manifest->{$k}->%* )
	    {
		die "Key '$hk' under '$k' is not valid in $manifest_clause\n"
		    if $sch->{keymatch} && $hk !~ $sch->{keymatch};

		validate_manifest($manifest_clause, $manifest->{$k}{$hk}, $sch->{schema}) if $sch->{schema};
	    }
	}
    }
}

my $last_req_time;

# Requests a CVE info from NVD. Dies on failure. Returns hash containing decoded
# CVE data

sub get_cves($)
{
    my $cpe   = shift;
    my %query = (
	apiKey         => $API_KEY,
	cpeMatchString => $cpe,
    );
    my $url = 'https://services.nvd.nist.gov/rest/json/cves/1.0/?' .
	      join('&', map {qq|$_=$query{$_}|} keys %query);

    # Honor the NVD API rate policy
    my $current_time = Time::HiRes::time();
    Time::HiRes::sleep(0.6 - ($current_time - $last_req_time))
	if $last_req_time && $current_time - $last_req_time < 0.6;

    $last_req_time = $current_time;

    my $res = HTTP::Tiny->new->get($url);

    die "Failed to request $url" unless $res->{success};

    decode_json($res->{content});
}

# Given CVE's {description}{description_data}, returns a human-readable string
# describing a vulnerability, by the way hacking CVE markdown to present a
# valid AsciiDoc

sub format_description($)
{
    my $desc = shift;
    my $res;

    for (@$desc)
    {
	$res = $_->{value} and last if $_->{lang} eq 'en';
    }

    unless ($res)
    {
	for (@$desc)
	{
	    $res = $_->{value} and last if !$_->{lang};
	}

	$res = $desc->[0]{value} unless $res; # Better than nothing
    }

    $res =~ s/~/\\~/g;
    $res;
}

my %libids_met;
my @generated_docs;

# Generates AsciiDoc documentation snippet for a single CVE

sub gendoc($$$$)
{
    my ( $cveid, $manifest, $builds, $descr ) = @_;

    my $res = "=== https://nvd.nist.gov/vuln/detail/${cveid}[$cveid]\n\n";

    $res .= "Component affected:: $manifest->{name}\n\n";
    $res .= "Builds affected:: " . join(', ', map { $BUILD_NAMES{$_} // $_ } @$builds) . "\n\n";
    $res .= "$descr\n\n";
    $res .= "'''\n\n";

    $res;
}

# Given a manifest, extracts all the library identifiers (buildSource-s) from
# it, marks them met and returns them as a list

sub getmark_libs($)
{
    my $manifest = shift;

    if ( $manifest->{buildSource} )
    {

	my @libids
	    = ref $manifest->{buildSource} eq 'ARRAY'
	    ? $manifest->{buildSource}->@*
	    : ( $manifest->{buildSource} );

	$libids_met{$_} = 1 for @libids;

	return @libids;
    }

    ();
}

# Given a manifest, returns a reference to a hash mapping library versions to
# an array of build idenfitiers which are using that version

sub versions_builds($)
{
    my $manifest = shift;
    my ( %versions, @versions, %version_to_sourcesets, %version_map );

    if ( $manifest->{type} eq 'external' )
    {
	for my $libid ( getmark_libs($manifest) )
	{
	    for my $ver ( keys $libinfo{$libid}->%* )
	    {
		$ver =~ s/^=//;
		push @versions, $ver;
		$version_to_sourcesets{$ver} = $libinfo{$libid}{$ver};
	    }
	}
    }
    elsif ( $manifest->{type} eq 'embedded' )
    {
	@versions
	    = ref $manifest->{version} eq 'ARRAY'
	    ? $manifest->{version}->@*
	    : ( $manifest->{version} );
    }

    if ( $manifest->{versionMap} )
    {
	my @version_map
	    = ref $manifest->{versionMap} eq 'ARRAY'
	    ? $manifest->{versionMap}->@*
	    : ( $manifest->{versionMap} );

	for (@version_map)
	{
	    my ( $from, $to ) = /^([\w\.-]+)\s*->\s*([\w\.-]+)$/;
	    $version_map{$from} = $to;
	}
    }

    for my $ver (@versions)
    {
	my @builds_affected = ('ALL');

	if ( $manifest->{type} eq 'external' && !$version_to_sourcesets{$ver}{default} )
	{
	    my %builds;

	    for my $sourceset ( keys $version_to_sourcesets{$ver}->%* )
	    {
		$builds{$_} = 1 for $sourceset_to_builds{$sourceset}->@*;
	    }

	    @builds_affected = sort keys %builds;

	}

	$versions{ $version_map{$ver} // $ver } = \@builds_affected;
    }

    \%versions;

}

# Given a review date (YYYY-MM-DD string) calculates the next review date,
# adding $REVIEW_EVERY_MONTHS months

sub next_review_date($)
{
    my @review_date = split /-/, shift;

    strftime('%Y-%m-%d',
	localtime(
	    mktime(
		0, 0, 0, $review_date[2],
		$review_date[1] - 1 + $REVIEW_EVERY_MONTHS,
		$review_date[0] - 1900
	    )
	)
    );
}

# Performs checks of single manifest. Parameters are manifest itself and
# manifest file path (for logging). Dies on faiulre. Return value is undefined.

sub run_manifest_check($$)
{
    my ( $manifest, $manifest_relpath ) = @_;

    unless ( $manifest->{cpe23} )
    {
	logd "  Found managed dependency '$manifest->{name}' without a CPE";

	getmark_libs($manifest); # Just mark libs as met

	logp "Manifest for '$manifest->{name}' in $manifest_relpath has a review date in the future"
	    if $manifest->{reviewDate} gt $NOW;

	my $next_review_date = next_review_date($manifest->{reviewDate});

	logd "  Next review date: $next_review_date";

	logp "Manifest for '$manifest->{name}' in $manifest_relpath should be reviewed as of $next_review_date"
	    if $NOW ge $next_review_date;

	return;
    }

    my @cpe_query = split /:/, $manifest->{cpe23};
    my $versions  = versions_builds($manifest);

    for my $ver ( sort keys %$versions )
    {
	my $cpe = join ':', @cpe_query[ 0 .. 4 ], $ver;

	logd "  Requesting CVEs with CPE $cpe for '$manifest->{name}' version $ver";

	my $cves = get_cves($cpe);

	if ( $cves->{totalResults} )
	{
	    for my $cve ( $cves->{result}{CVE_Items}->@* )
	    {
		my $cveid = $cve->{cve}{CVE_data_meta}{ID};

		if ( $manifest->{CVEs} && $manifest->{CVEs}{$cveid} )
		{
		    logd "    Found managed $cveid";

		    if ( any { $manifest->{CVEs}{$cveid}{status} eq $_ } qw(Active Observed) )
		    {
			logp "$cveid for '$manifest->{name}' in $manifest_relpath has a review date in the future"
			    if $manifest->{CVEs}{$cveid}{reviewDate} gt $NOW;

			my $next_review_date = next_review_date($manifest->{CVEs}{$cveid}{reviewDate});

			logd "    Next review date: $next_review_date";

			logp "$cveid for '$manifest->{name}' in $manifest_relpath should be reviewed as of $next_review_date"
			    if $NOW ge $next_review_date;
		    }

		    if ( $manifest->{CVEs}{$cveid}{status} eq 'Active' && $GENDOC )
		    {
			my $descr = format_description($cve->{cve}{description}{description_data});
			push @generated_docs, gendoc($cveid, $manifest, $versions->{$ver}, $descr);
		    }
		}
		else
		{
		    logp "Unmanaged $cveid found for '$manifest->{name}', version $ver, in $manifest_relpath, " .
			 "builds affected: " . join( ', ', $versions->{$ver}->@* ) .
			 " (see https://nvd.nist.gov/vuln/detail/$cveid)";
		}
	    }
	}
    }
}

# Processes a single directory. Silently returns if no manifest file found. Dies
# if manifest file is empty, unreadable or is not a valid YAML, or if it fails to
# validate the manifest. Logs found problems to STDERR.

sub process_dir($)
{
    my $dir           = shift;
    my $manifest_file = "$dir/SecurityManifest.yml";

    logd("  No manifest file found"), return unless -f $manifest_file;

    my $manifest_relpath = relpath($manifest_file);
    my @manifests = YAML::LoadFile($manifest_file) or die "Cannot read $manifest_relpath\n";
    die "Empty security manifest $manifest_relpath\n" unless @manifests;

    for my $manifest (@manifests)
    {
	next unless %$manifest; # Allow totally empty manifests, as a separator

	my $manifest_clause = (
	    $manifest->{name} && !ref $manifest->{name}
		? "manifest '$manifest->{name}'"
		: 'unnamed manifest'
	) . " in $manifest_relpath";

	validate_manifest($manifest_clause, $manifest, $MANIFEST_SCHEMA);
	run_manifest_check($manifest, $manifest_relpath);
    }
}

# Traverses directory tree, calling process_dir() for every directory. Ignores
# hidden directories (starting with '.')

sub traverse_dir($);

sub traverse_dir($)
{
    my $dir = shift;

    logd "Entering $dir";
    process_dir($dir);

    opendir(my $dh, $dir) or die "Cannot open $dir: $!\n";

    while ( readdir $dh )
    {
	next if /^\./;
	my $entry = "$dir/$_";
	traverse_dir($entry) if -d $entry;
    }

    closedir $dh;
}

traverse_dir($ROOT);

# Check if there's a dependency in build definition which is not present in any
# security manifest

for (keys %libinfo) {
    logp "Build dependency '$_' is mentioned in the build definition but is not managed by any security manifest"
    	unless $libids_met{$_};
}

if ( $GENDOC && !$PCNT )
{
    open my $outfh, '>', $GENDOC or die "Cannot open $GENDOC for writing: $!\n";
    print $outfh $_ for @generated_docs;
    close $outfh;
}

exit 1 if $PCNT;
