// reporterr.cc            see license.txt for copyright and terms of use
// code for reporterr.h

#include "reporterr.h"      // this module


// --------------------- SilentReportError -------------------------
SilentReportError::SilentReportError()
  : errors(0),
    warnings(0)
{}

void SilentReportError::reportError(rostring str)
{
  errors++;
}

void SilentReportError::reportWarning(rostring str)
{
  warnings++;
}

SilentReportError silentReportError;


// --------------------- SimpleReportError -------------------------
void SimpleReportError::reportError(rostring str)
{
  SilentReportError::reportError(str);
  cout << "error: " << str << endl;
}

void SimpleReportError::reportWarning(rostring str)
{
  SilentReportError::reportWarning(str);
  cout << "warning: " << str << endl;
}

SimpleReportError simpleReportError;


// EOF
