/*
 *  This is a sample plugin module
 *
 *  It extends the IBM PC processor module to disassemble some NEC V20 instructions
 *
 *  This is a sample file, it supports just two instructions!
 *
 */

#include <ida.hpp>
#include <idp.hpp>
#include <name.hpp>
#include <bytes.hpp>
#include <loader.hpp>
#include <kernwin.hpp>
#include <netnode.hpp>
#include <struct.hpp>
#define DEBUGON 1
#define WIN32_LEAN_AND_MEAN
#include <windows.h>

#include "arm.h"


//----------------------------------------------------------------------

static uint32 _declspec(naked) rdtsc() {
	_asm {
		rdtsc
		ret
	}
}


//--------------------------------------------------------------------------
// Analyse an instruction and fill the 'cmd' structure
int ana(void)
{
	char s[1024];

//	s = netnode(ea).supval(LUDDE_NETNODE_SUPVAL);
//	if (s) return ana_manual(s);
	
//	msg("ana %x\n", cmd.ea);
	if (netnode(ea).supval(PSEUDO_NETNODE_SUPVAL,s,sizeof(s)) != -1) {
		return ana_pseudo((byte*)s);
	}

//	return 0;
	return ana_simplify();
}


//--------------------------------------------------------------------------
// This callback is called for IDP (processor module) notification events
// Here we extend the processor module to disassemble opcode 0xFF
// (This is a hypothetical example)
// There are 2 approaches for the extensions:
//  A. Quick & dirty
//       you implemented custom_ana and custom_out
//       The first checks if the instruction is valid
//       The second generates its text
//  B. Thourough and clean
//       you implement all callbacks
//       custom_ana fills the 'cmd' structure
//       custom_emu creates all xrefs using ua_add_[cd]ref functions
//       custom_out generates the instruction representation
//         (only if the instruction requires special processing
//          or the processor module can't handle the custom instruction for any reason)
//       custom_outop generates the operand representation (only if the operand requires special processing)
//       custom_mnem returns the instruction mnemonics (without the operands)
// The main difference between these 2 approaches is in the presence of cross-references
// and the amount of special processing required by the new instructions

// The quick & dirty approach
// We just produce the instruction mnemonics along with its operands
// No cross-references are created. No special processing.

static int dirty_extension_callback(void * /*user_data*/, int event_id, va_list va)
{
  switch ( event_id )
  {
    case ph.custom_ana:
      {
        ea = cmd.ea;
        int length = ana();
        if ( length ) {
					cmd.size = length;
          return length+1;       // event processed
        }
      }
      break;

    case ph.custom_mnem:
      if ( cmd.itype >= CUSTOM_CMD_ITYPE )
      {
        char *buf   = va_arg(va, char *);
        size_t size = va_arg(va, size_t);
        qstrncpy(buf, get_insn_mnem(),size);
        return 2;
      }
      break;

		case ph.custom_emu:
			if (cmd.itype >= CUSTOM_CMD_ITYPE) {
				if (cmd.itype == ARM_manual) {
					emu_manual();
				} else if (cmd.itype == ARM_pseudo) {
					emu_pseudo();
				} else {
					emu_simplify();
				}
				return 2;
			}
			break;

		case ph.custom_outop:
			if (cmd.itype == ARM_pseudo) {
				if (outop_pseudo(va_arg(va, op_t *)))
					return 2;
			} else if (cmd.itype >= CUSTOM_CMD_ITYPE) {
				if (outop_simplify(va_arg(va, op_t *)))
					return 2;
			}
			break;
			
		case ph.custom_out:
			if (cmd.itype >= CUSTOM_CMD_ITYPE) {
				if (cmd.itype == ARM_manual) {
					out_manual();
				} else if (cmd.itype == ARM_pseudo) {
					out_pseudo();
				} else {
					out_simplify();
				}
				return 2;
			}
			break;
  }
  return 0;                     // event is not processed
}

//--------------------------------------------------------------------------
//
//      Initialize.
//
//      IDA will call this function only once.
//      If this function returns PLGUIN_SKIP, IDA will never load it again.
//      If this function returns PLUGIN_OK, IDA will unload the plugin but
//      remember that the plugin agreed to work with the database.
//      The plugin will be loaded again if the user invokes it by
//      pressing the hotkey or selecting it from the menu.
//      After the second load the plugin will stay on memory.
//      If this function returns PLUGIN_KEEP, IDA will keep the plugin
//      in the memory. In this case the initialization function can hook
//      into the processor module and user interface notification points.
//      See the hook_to_notification_point() function.
//
//      In this example we check the processor type and make the decision.
//      You may or may not check any other conditions to decide what you do:
//      whether you agree to work with the database or not.
//

static bool hooked = false;
static netnode nec_node;
static const char node_name[] = "$ ludde arm params";

struct sample_info_t
{
  TForm *form;
  TCustomControl *cv;
  strvec_t sv;
};
int idaapi ui_callback(void *ud, int code, va_list va)
{
  sample_info_t *si = (sample_info_t *)ud;
  switch ( code )
  {
    // how to implement a simple hint callback
    case ui_get_custom_viewer_hint:
      
       /* TCustomControl *viewer = va_arg(va, TCustomControl *);
        place_t *place         = va_arg(va, place_t *);
        int *important_lines   = va_arg(va, int *);
        qstring &hint          = *va_arg(va, qstring *);
        if ( si->cv == viewer ) // our viewer
        {
          if ( place == NULL )
            return 0;
          simpleline_place_t *spl = (simpleline_place_t *)place;
          hint.sprnt("Hint for line %d", spl->n);
          *important_lines = 1;
          return 1;
        }
      }*/
		  break;
    case ui_tform_invisible:
      // a form is being closed, free the resources
      delete si;
      break;
  }
  return 0;
}

//---------------------------------------------------------------------------
// Create a custom view window


  static struct
{
  const char *text;
  bgcolor_t color;
} const sample_text[] =
{
  { "Hello decompiled view!",                                         0xFFFFFF },
  
};

// Structure to keep all information about the our sample view


//---------------------------------------------------------------------------
// Sample callback function for the right-click menu


//---------------------------------------------------------------------------


//---------------------------------------------------------------------------
#define add_popup add_custom_viewer_popup_item

//---------------------------------------------------------------------------

//---------------------------------------------------------------------------
// This callback will be called each time the keyboard cursor position
// is changed


//--------------------------------------------------------------------------
TForm *form;
HWND hwnd;
int init(void)
{
	form=0;
	hwnd=0;
  if ( ph.id != PLFM_ARM ) return PLUGIN_SKIP;
  
	msg("Thumb decompiler v0.1 by Ludvig Strigeus <luddes(at)gmail(dot)com>\n");
	
	nec_node.create(node_name);
  hooked = nec_node.altval(0) != 0;
  if ( hooked )
  {
    hook_to_notification_point(HT_IDP, dirty_extension_callback, NULL);

  // set the handlers so we can communicate with it
 
  // also set the ui event callback
 
  // finally display the form on the screen

    msg("Thumb decompiler is enabled\n");
		ph.can_have_type = NULL;
		ph.cmp_opnd = NULL;
		ph.is_sp_based = NULL;
    return PLUGIN_KEEP;
  }
  return PLUGIN_OK;
}

//--------------------------------------------------------------------------
//      Terminate.
//      Usually this callback is empty.
//      The plugin should unhook from the notification lists if
//      hook_to_notification_point() was used.
//
//      IDA will call this function when the user asks to exit.
//      This function won't be called in the case of emergency exits.

void term(void)
{
  unhook_from_notification_point(HT_IDP, dirty_extension_callback);
}

void toggle_comment()
{
	ea_t ea = get_screen_ea();

	describe(ea, true, ";");
}

bool dodecomp(int entry)
{

	

	HINSTANCE inst = LoadLibrary("plugins\\decomp.dll");
	if (!inst) return false;

	void *proc = GetProcAddress(inst, "LUDDE");
	if (!proc) { FreeLibrary(inst); return false; }

	typedef void MyFunc(int entry );

	((MyFunc*)*(void**)proc)(entry);

	FreeLibrary(inst);
#ifdef DEBUGON

	hwnd = NULL;
			if(0==form){  
			form = create_tform("Decompiled view", &hwnd);
			msg("form: %x\n", form);
			  if ( hwnd == NULL )
			  {
				warning("Could not create custom view window\n"
						"perhaps it is open?\n"
						"Switching to it.");
				form = find_tform("Decompiled view");
				if ( form != NULL )
				  switchto_tform(form, true);
				else 
					return 1;  
			  }
				// allocate block to hold info about our sample view
		  sample_info_t *si = new sample_info_t;
		  si->form = form;
		  // prepare the data to display. we could prepare it on the fly too.
		  // but for that we have to use our own custom place_t class decendant.
		  for ( int i=0; i < qnumber(sample_text); i++ )
		  {
			si->sv.push_back(simpleline_t("")); // add empty line
			si->sv.push_back(simpleline_t(sample_text[i].text));
			si->sv.back().bgcolor = sample_text[i].color;
		  }
		  // create two place_t objects: for the minimal and maximal locations
		  simpleline_place_t s1;
		  simpleline_place_t s2(si->sv.size()-1);
		  // create a custom viewer
		  si->cv = create_custom_viewer("", (TWinControl *)form, &s1, &s2, &s1, 0, &si->sv);
		  // set the handlers so we can communicate with it
		  set_custom_viewer_handlers(si->cv, NULL, NULL, NULL, NULL, NULL, si);
		  // also set the ui event callback
		  hook_to_notification_point(HT_UI, ui_callback, si);
		  // finally display the form on the screen
		  open_tform(form, FORM_TAB|FORM_MENU|FORM_RESTORE);
			}

	}

#endif
	return true;
}

//--------------------------------------------------------------------------
//
//      The plugin method
//
//      This is the main function of plugin.
//
//      It will be called when the user selects the plugin.
//
//              arg - the input argument, it can be specified in
//                    plugins.cfg file. The default is zero.
//
//
 void Contral(int overridea=0){
	
	 
	 
	 if ( hooked ){
				unhook_from_notification_point(HT_IDP, dirty_extension_callback);
			}
			else
			{
			
				hook_to_notification_point(HT_IDP, dirty_extension_callback, NULL);

			}
			hooked = !hooked;
			nec_node.create(node_name);
			nec_node.altset(0, hooked);
			msg("Thumb decompiler is now %s\n", hooked ? "enabled" : "disabled");

 }
void Enable(){


		   if ( hooked ){
				unhook_from_notification_point(HT_IDP, dirty_extension_callback);
			}
			else
			{
			
				hook_to_notification_point(HT_IDP, dirty_extension_callback, NULL);

			}
			hooked = !hooked;
			nec_node.create(node_name);
			nec_node.altset(0, hooked);
			msg("Thumb decompiler is now %s\n", hooked ? "enabled" : "disabled");
			if(hooked){
							if (!dodecomp(0))
				msg("DLL load error\n");

			}
}
void run(int arg)
{
	if(!hooked) {

	Enable();
	}

	if (!dodecomp(arg))
			msg("DLL load error\n");


	/*switch(arg) {
	case 0:
		if (GetAsyncKeyState(VK_CONTROL) < 0) {
		
		} else {
			//domanual();
			if (!dodecomp(0))
				msg("DLL load error\n");

		}
		break;

	case 1:
	case 2:
	case 3:
	case 4:
	case 5:
	case 6:
	case 7:
		if (!dodecomp(arg))
			msg("DLL load error\n");
		break;		
	

	}*/
}

//--------------------------------------------------------------------------
char comment[] = "ARM Extension by ludde\n Renewed by interdpth";

char help[] =
        "A sample plugin module\n"
        "\n"
        "This module shows you how to create plugin modules.\n"
        "\n";


//--------------------------------------------------------------------------
// This is the preferred name of the plugin module in the menu system
// The preferred name may be overriden in plugins.cfg file

char wanted_name[] = "ARM Extension";


// This is the preferred hotkey for the plugin module
// The preferred hotkey may be overriden in plugins.cfg file
// Note: IDA won't tell you if the hotkey is not correct
//       It will just disable the hotkey.

char wanted_hotkey[] = "Z";


//--------------------------------------------------------------------------
//
//      PLUGIN DESCRIPTION BLOCK
//
//--------------------------------------------------------------------------

extern "C" plugin_t PLUGIN = {
  IDP_INTERFACE_VERSION,
  0,                    // plugin flags
  init,                 // initialize

  term,                 // terminate. this pointer may be NULL.

  run,                  // invoke plugin

  comment,              // long comment about the plugin
                        // it could appear in the status line
                        // or as a hint

  help,                 // multiline help about the plugin

  wanted_name,          // the preferred short name of the plugin
  wanted_hotkey         // the preferred hotkey to run the plugin
};
