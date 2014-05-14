(** generate core images **)

fun make_lego b msg =
  let
    val datemsg =
      let                    (* get current date *)
	val (is,os) = execute ("/usr/bin/date",[])
	val date = input_line is
	val _ = (close_in is; close_out os)
      in (date,msg)
      end
    fun head (date,msg) =
      (print "\n";
       print "Standard ML with LEGO\n";
       print ("Generated  "^date);
       print ("using "^System.version^"\n");
       if msg <> "" then print (msg^"\n") else ();
       print "use command 'Help' for info on new commands.\n")
    val arch =
      let 
	fun check [] = (message"No entry `LEGOARCH' in environment;\
                               \ core images placed in subdirectory `bin'.";
			"bin")
	  | check (h::t) =
	    if (substring(h,0,9) = "LEGOARCH=" handle Substring => false)
	      then substring(h,9,size h - 9)
	    else check t
      in check (System.environ())
      end
    fun LEGO (x,y) = (head datemsg; 
                      Init.Init_raw "XCC";
		      lego())
  in 
    if exportML (arch^"/legoML")
      then LEGO([],[])
    else (print("\n** legoML written in subdirectory `"^arch^"' **\n");
	  if b then (print("\n** making lego in subdirectory `"^arch^"' ...\n");
		     exportFn((arch^"/lego"),LEGO))
	  else ())
  end;
