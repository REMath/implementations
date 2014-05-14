#!/usr/bin/perl -w

use strict;
use CGI qw(:standard);
use File::Copy;

sub exit_with {
    my $msg = shift or die;

    print("document.getElementById('job_server').innerHTML = '$msg';\n");
    exit;
}

sub check_param {
    my $param = shift or die;
    my $value = param($param) or exit_with "Need CGI parameter: $param";
    return $value;
}

print "Content-type: text/javascript\n\n";

# check to make sure the job directories exist.
die if not (-d "jobs");
die if not (-d "jobs_todo");

my $report = check_param('report');
my $ext = check_param('ext');
my $link = check_param('link');
my $prev = check_param('prev');
my $next = check_param('next');

if ($report =~ /[\n\"\']/) {
    exit_with "ERROR: Bad character in report";
}
if ($ext =~ /[^A-Z]/ || length($ext) > 10) {
    exit_with "ERROR: Invalid extension";
}
if ($link =~ /[^a-zA-Z0-9_]/) {
    exit_with "ERROR: Bad character in link";
}
if ($prev =~ /[^a-zA-Z0-9_]/) {
    exit_with "ERROR: Bad character in prev";
}
if ($next =~ /[^a-zA-Z0-9_]/) {
    exit_with "ERROR: Bad character in next";
}

my $hook = param('hook');
my $text = param('text');
my $trust = param('trust');

if (defined $hook) {
    exit_with "Need CGI parameter: text" if (not (defined $text));
    exit_with "Need CGI parameter: trust" if (not (defined $trust));

    # hook will be checked further downstream, text will not get
    # anymore checking.
    if ($hook =~ /[\n\r]/) {
        exit_with "ERROR: Invalid hook";
    }
    if ($text =~ /[\n\r\'\"]/) {
        exit_with "ERROR: Invalid text";
    }

    if ($text eq "") {
	exit_with "ERROR: Annotation text is blank";
    }
    if ($trust ne "true" && $trust ne "false") {
	exit_with "ERROR: Invalid trust";
    }
}

if ($ext eq "NEW") {
    # new job, make an extension for it.
    $ext = "";
    my @chars = ('A'..'Z');
    for (my $i = 0; $i < 10; $i++) {
        $ext .= $chars[rand @chars];
    }

    open(OUT, "> $ext.job");
    print OUT "$ext\n";
    print OUT "$report\n";
    print OUT "$link\n";
    print OUT "$prev\n";
    print OUT "$next\n";
    if (defined $hook) {
        print OUT "$hook\n";
        print OUT "$text\n";
        print OUT "$trust\n";
    }
    close(OUT);
    move("$ext.job", "jobs_todo/$ext.job");

    print "setTimeout('refreshJob(\"$ext\")', 3000);\n";
    exit_with "Waiting to start...";
}

if (-e "jobs/$ext.done") {
    open(IN, "< jobs/$ext.done");
    my $result = <IN>;
    chomp $result;
    close(IN);

    exit_with $result;
}

if (-e "jobs/$ext.job") {
    my $age = -M "jobs/$ext.job";

    # age is in days, get it in seconds.
    $age = $age * 24.0 * 60.0 * 60.0;

    if ($age > 180) {
	exit_with "Timeout waiting for result";
    }

    print "setTimeout('refreshJob(\"$ext\")', 3000);\n";
    exit_with "Analysis in progress... ($age seconds)";
}

if (-e "jobs_todo/$ext.job") {
    my $age = -M "jobs_todo/$ext.job";

    # age is in days, get it in seconds.
    $age = $age * 24.0 * 60.0 * 60.0;

    if ($age > 60) {
	exit_with "Timeout waiting to start";
    }

    print "setTimeout('refreshJob(\"$ext\")', 3000);\n";
    exit_with "Waiting to start... ($age seconds)";
}

exit_with "Unknown job";
