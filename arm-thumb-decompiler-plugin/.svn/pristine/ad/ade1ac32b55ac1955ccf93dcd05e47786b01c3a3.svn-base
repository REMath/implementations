/*

  This file is NOT used by the plugin.
  It contains the implementation of the simpleline_place_t class from IDA.
  Just for your info how to derive classes from place_t.

*/


#include <ida.hpp>
#include <kernwin.hpp>

// shortcut to make the text more readable
typedef simpleline_place_t sp_t;

//--------------------------------------------------------------------------
// Short information about the current location.
// It will be displayed in the status line
void ida_export simpleline_place_t__print(const sp_t *ths, void *,char *buf, size_t bufsize)
{
  qsnprintf(buf, bufsize, "%d", ths->n);
}

//--------------------------------------------------------------------------
// Convert current location to 'uval_t'
uval_t ida_export simpleline_place_t__touval(const sp_t *ths, void *)
{
  return ths->n;
}

//--------------------------------------------------------------------------
// Make a copy
place_t *ida_export simpleline_place_t__clone(const sp_t *ths)
{
  simpleline_place_t *p = qnew(simpleline_place_t);
  if ( p == NULL )
    nomem("simpleline_place");
  memcpy(p, ths, sizeof(*ths));
  return p;
}

//--------------------------------------------------------------------------
// Copy from another simpleline_place_t object
void ida_export simpleline_place_t__copyfrom(sp_t *ths, const place_t *from)
{
  simpleline_place_t *s = (simpleline_place_t *)from;
  ths->n     = s->n;
  ths->lnnum = s->lnnum;
}

//--------------------------------------------------------------------------
// Create a simpleline_place_t object at the specified address
// with the specified data
place_t *ida_export simpleline_place_t__makeplace(const sp_t *, void *, uval_t x, short lnnum)
{
  static simpleline_place_t p;
  p.n     = x;
  p.lnnum = lnnum;
  return &p;
}

//--------------------------------------------------------------------------
// Compare two simpleline_place_t objects
// Return -1, 0, 1
int ida_export simpleline_place_t__compare(const sp_t *ths, const place_t *t2)
{
  simpleline_place_t *s = (simpleline_place_t *)t2;
  return ths->n - s->n;
}

//--------------------------------------------------------------------------
// Check if the location data is correct and if not, adjust it
void ida_export simpleline_place_t__adjust(sp_t *ths, void *ud)
{
  strvec_t &sv = *(strvec_t *)ud;
  if ( ths->n >= sv.size() )
  {
    ths->n = 0;
    ths->lnnum = 0;
  }
}

//--------------------------------------------------------------------------
// Move to the previous location
bool ida_export simpleline_place_t__prev(sp_t *ths, void *)
{
  if ( ths->n == 0 )
    return false;
  ths->n--;
  return true;
}

//--------------------------------------------------------------------------
// Move to the next location
bool ida_export simpleline_place_t__next(sp_t *ths, void *ud)
{
  strvec_t &sv = *(strvec_t *)ud;
  if ( ths->n >= sv.size() )
    return false;
  ths->n++;
  return true;
}

//--------------------------------------------------------------------------
// Are we at the beginning of the data?
bool ida_export simpleline_place_t__beginning(const sp_t *ths, void *)
{
  return ths->n == 0;
}

//--------------------------------------------------------------------------
// Are we at the end of the data?
bool ida_export simpleline_place_t__ending(const sp_t *ths, void *ud)
{
  strvec_t &sv = *(strvec_t *)ud;
  return ths->n >= sv.size()-1;
}

//--------------------------------------------------------------------------
// Generate text for the current location
int ida_export simpleline_place_t__generate(
        const sp_t *ths,
        void *ud,
        char *lines[],
        int maxsize,
        int *default_lnnum,
        color_t *prefix_color,
        bgcolor_t *bg_color)
{
  strvec_t &sv = *(strvec_t *)ud;
  int idx = ths->n;
  if ( idx >= sv.size() || maxsize <= 0 )
    return 0;
  lines[0] = qstrdup(sv[idx].line.c_str());
  *prefix_color = sv[idx].color;
  *bg_color = sv[idx].bgcolor;
  *default_lnnum = 0;
  return 1; // generated one line
}

