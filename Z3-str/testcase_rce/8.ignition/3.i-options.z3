(declare-variable	v_92730d8		bool)
(declare-variable	v_927318c		bool)
(declare-variable	v_9273220		bool)
%----------------------------------------
(declare-variable	T_local__POST		(_ BitVec 1) )
(declare-variable	T_local__POST_i_author		(_ BitVec 1) )
(declare-variable	T_local__POST_i_book		(_ BitVec 1) )
(declare-variable	T_local__POST_i_description		(_ BitVec 1) )
(declare-variable	T_local__POST_i_game		(_ BitVec 1) )
(declare-variable	T_local__POST_i_gravatar		(_ BitVec 1) )
(declare-variable	T_local__POST_i_id		(_ BitVec 1) )
(declare-variable	T_local__POST_i_identica		(_ BitVec 1) )
(declare-variable	T_local__POST_i_lang		(_ BitVec 1) )
(declare-variable	T_local__POST_i_pass		(_ BitVec 1) )
(declare-variable	T_local__POST_i_skin		(_ BitVec 1) )
(declare-variable	T_local__POST_i_submit		(_ BitVec 1) )
(declare-variable	T_local__POST_i_suri		(_ BitVec 1) )
(declare-variable	T_local__POST_i_title		(_ BitVec 1) )
(declare-variable	T_local__POST_i_twitter		(_ BitVec 1) )
(declare-variable	T_local__POST_i_uri		(_ BitVec 1) )
(declare-variable	T_v_92733b4		(_ BitVec 1) )
(declare-variable	T_v_9273454		(_ BitVec 1) )
(declare-variable	T_v_92735d4		(_ BitVec 1) )
(declare-variable	T_v_9273674		(_ BitVec 1) )
(declare-variable	T_v_92737f4		(_ BitVec 1) )
(declare-variable	T_v_9273894		(_ BitVec 1) )
(declare-variable	T_v_9273a14		(_ BitVec 1) )
(declare-variable	T_v_9273ab4		(_ BitVec 1) )
(declare-variable	T_v_9273c34		(_ BitVec 1) )
(declare-variable	T_v_9273cd4		(_ BitVec 1) )
(declare-variable	T_v_9273e54		(_ BitVec 1) )
(declare-variable	T_v_9273ef4		(_ BitVec 1) )
(declare-variable	T_v_9274074		(_ BitVec 1) )
(declare-variable	T_v_9274114		(_ BitVec 1) )
(declare-variable	T_v_9274294		(_ BitVec 1) )
(declare-variable	T_v_9274334		(_ BitVec 1) )
(declare-variable	T_v_92744b4		(_ BitVec 1) )
(declare-variable	T_v_9274554		(_ BitVec 1) )
(declare-variable	T_v_92746d4		(_ BitVec 1) )
(declare-variable	T_v_9274774		(_ BitVec 1) )
(declare-variable	T_v_92748f4		(_ BitVec 1) )
(declare-variable	T_v_9274994		(_ BitVec 1) )
(declare-variable	T_v_9274b14		(_ BitVec 1) )
(declare-variable	T_v_9274bb4		(_ BitVec 1) )
(declare-variable	T_v_9274d34		(_ BitVec 1) )
(declare-variable	T_v_9274dd4		(_ BitVec 1) )
(declare-variable	T_v_9274f54		(_ BitVec 1) )
(declare-variable	T_v_9274ff4		(_ BitVec 1) )
%----------------------------------------
(declare-variable	local__POST		Int)
(declare-variable	v_9275094		Int)
%========================================

% ASSERT( v_92730d8 <=> TRUE );
(assert (=  v_92730d8  true  ) )
% ASSERT( T_local__POST_i_submit = T_local__POST );
(assert (=  T_local__POST_i_submit  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( v_9273220 <=> v_927318c );
(assert (=  v_9273220  v_927318c  ) )
% ASSERT( T_v_9274ff4 = 0bin00000000000000000000000000000001 );
(assert (=  T_v_9274ff4  #b1  ) )
% ASSERT( T_v_9274ff4 = T_v_9274f54 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9274ff4   (bvor T_v_9274f54 #b0)   ) )
% ASSERT( T_v_9274f54 = T_v_9274dd4 | T_local__POST_i_lang);
(assert (=  T_v_9274f54   (bvor T_v_9274dd4 T_local__POST_i_lang)   ) )
% ASSERT( T_v_9274dd4 = T_v_9274d34 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9274dd4   (bvor T_v_9274d34 #b0)   ) )
% ASSERT( T_v_9274d34 = T_v_9274bb4 | T_local__POST_i_game);
(assert (=  T_v_9274d34   (bvor T_v_9274bb4 T_local__POST_i_game)   ) )
% ASSERT( T_v_9274bb4 = T_v_9274b14 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9274bb4   (bvor T_v_9274b14 #b0)   ) )
% ASSERT( T_v_9274b14 = T_v_9274994 | T_local__POST_i_book);
(assert (=  T_v_9274b14   (bvor T_v_9274994 T_local__POST_i_book)   ) )
% ASSERT( T_v_9274994 = T_v_92748f4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9274994   (bvor T_v_92748f4 #b0)   ) )
% ASSERT( T_v_92748f4 = T_v_9274774 | T_local__POST_i_identica);
(assert (=  T_v_92748f4   (bvor T_v_9274774 T_local__POST_i_identica)   ) )
% ASSERT( T_v_9274774 = T_v_92746d4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9274774   (bvor T_v_92746d4 #b0)   ) )
% ASSERT( T_v_92746d4 = T_v_9274554 | T_local__POST_i_twitter);
(assert (=  T_v_92746d4   (bvor T_v_9274554 T_local__POST_i_twitter)   ) )
% ASSERT( T_v_9274554 = T_v_92744b4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9274554   (bvor T_v_92744b4 #b0)   ) )
% ASSERT( T_v_92744b4 = T_v_9274334 | T_local__POST_i_gravatar);
(assert (=  T_v_92744b4   (bvor T_v_9274334 T_local__POST_i_gravatar)   ) )
% ASSERT( T_v_9274334 = T_v_9274294 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9274334   (bvor T_v_9274294 #b0)   ) )
% ASSERT( T_v_9274294 = T_v_9274114 | T_local__POST_i_skin);
(assert (=  T_v_9274294   (bvor T_v_9274114 T_local__POST_i_skin)   ) )
% ASSERT( T_v_9274114 = T_v_9274074 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9274114   (bvor T_v_9274074 #b0)   ) )
% ASSERT( T_v_9274074 = T_v_9273ef4 | T_local__POST_i_author);
(assert (=  T_v_9274074   (bvor T_v_9273ef4 T_local__POST_i_author)   ) )
% ASSERT( T_v_9273ef4 = T_v_9273e54 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9273ef4   (bvor T_v_9273e54 #b0)   ) )
% ASSERT( T_v_9273e54 = T_v_9273cd4 | T_local__POST_i_id);
(assert (=  T_v_9273e54   (bvor T_v_9273cd4 T_local__POST_i_id)   ) )
% ASSERT( T_v_9273cd4 = T_v_9273c34 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9273cd4   (bvor T_v_9273c34 #b0)   ) )
% ASSERT( T_v_9273c34 = T_v_9273ab4 | T_local__POST_i_description);
(assert (=  T_v_9273c34   (bvor T_v_9273ab4 T_local__POST_i_description)   ) )
% ASSERT( T_v_9273ab4 = T_v_9273a14 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9273ab4   (bvor T_v_9273a14 #b0)   ) )
% ASSERT( T_v_9273a14 = T_v_9273894 | T_local__POST_i_title);
(assert (=  T_v_9273a14   (bvor T_v_9273894 T_local__POST_i_title)   ) )
% ASSERT( T_v_9273894 = T_v_92737f4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9273894   (bvor T_v_92737f4 #b0)   ) )
% ASSERT( T_v_92737f4 = T_v_9273674 | T_local__POST_i_suri);
(assert (=  T_v_92737f4   (bvor T_v_9273674 T_local__POST_i_suri)   ) )
% ASSERT( T_v_9273674 = T_v_92735d4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9273674   (bvor T_v_92735d4 #b0)   ) )
% ASSERT( T_v_92735d4 = T_v_9273454 | T_local__POST_i_uri);
(assert (=  T_v_92735d4   (bvor T_v_9273454 T_local__POST_i_uri)   ) )
% ASSERT( T_v_9273454 = T_v_92733b4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9273454   (bvor T_v_92733b4 #b0)   ) )
% ASSERT( T_v_92733b4 = 0bin00000000000000000000000000000000 | T_local__POST_i_pass);
(assert (=  T_v_92733b4   (bvor #b0 T_local__POST_i_pass)   ) )
% ASSERT( T_local__POST_i_pass = T_local__POST );
(assert (=  T_local__POST_i_pass  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_uri = T_local__POST );
(assert (=  T_local__POST_i_uri  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_suri = T_local__POST );
(assert (=  T_local__POST_i_suri  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_title = T_local__POST );
(assert (=  T_local__POST_i_title  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_description = T_local__POST );
(assert (=  T_local__POST_i_description  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_id = T_local__POST );
(assert (=  T_local__POST_i_id  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_author = T_local__POST );
(assert (=  T_local__POST_i_author  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_skin = T_local__POST );
(assert (=  T_local__POST_i_skin  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_gravatar = T_local__POST );
(assert (=  T_local__POST_i_gravatar  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_twitter = T_local__POST );
(assert (=  T_local__POST_i_twitter  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_identica = T_local__POST );
(assert (=  T_local__POST_i_identica  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_book = T_local__POST );
(assert (=  T_local__POST_i_book  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_game = T_local__POST );
(assert (=  T_local__POST_i_game  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_lang = T_local__POST );
(assert (=  T_local__POST_i_lang  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( v_92730d8 );
(assert v_92730d8 )
% ASSERT( v_9273220 );
(assert v_9273220 )

%========================================
(declare-variable	v_9274ff4		String)
(declare-variable	v_9274f54		String)
(declare-variable	v_9274dd4		String)
(declare-variable	local__POST_i_lang		String)
(declare-variable	v_9274d34		String)
(declare-variable	v_9274bb4		String)
(declare-variable	local__POST_i_game		String)
(declare-variable	v_9274b14		String)
(declare-variable	v_9274994		String)
(declare-variable	local__POST_i_book		String)
(declare-variable	v_92748f4		String)
(declare-variable	v_9274774		String)
(declare-variable	local__POST_i_identica		String)
(declare-variable	v_92746d4		String)
(declare-variable	v_9274554		String)
(declare-variable	local__POST_i_twitter		String)
(declare-variable	v_92744b4		String)
(declare-variable	v_9274334		String)
(declare-variable	local__POST_i_gravatar		String)
(declare-variable	v_9274294		String)
(declare-variable	v_9274114		String)
(declare-variable	local__POST_i_skin		String)
(declare-variable	v_9274074		String)
(declare-variable	v_9273ef4		String)
(declare-variable	local__POST_i_author		String)
(declare-variable	v_9273e54		String)
(declare-variable	v_9273cd4		String)
(declare-variable	v_9273c34		String)
(declare-variable	v_9273ab4		String)
(declare-variable	local__POST_i_description		String)
(declare-variable	v_9273a14		String)
(declare-variable	v_9273894		String)
(declare-variable	local__POST_i_title		String)
(declare-variable	v_92737f4		String)
(declare-variable	v_9273674		String)
(declare-variable	local__POST_i_suri		String)
(declare-variable	v_92735d4		String)
(declare-variable	v_9273454		String)
(declare-variable	local__POST_i_uri		String)
(declare-variable	v_92733b4		String)
(declare-variable   tmp       String)
(declare-variable   name       String)
(declare-variable   local__POST_i_id       String)
(declare-variable   local__POST_i_pass       String)



% ----------------------------------------------------------
% local__POST_i_submit := zYh_aNyStR
% v_927318c := "data/settings.php"
(assert (= name (Concat tmp ".php") ) )
(assert (= v_927318c (= name "data/settings.php") ) )
% v_9274ff4 := v_9274f54 ";\n\nrequire_once(template.php);\nrequire_once(lang/$language.php);"
(assert (= v_9274ff4 (Concat v_9274f54 "_^sc^_^n^_^n^require_once_template.php__^sc^_^n^require_once_lang/_^do^language.php__^sc^") ) )
% v_9274f54 := v_9274dd4 local__POST_i_lang
(assert (= v_9274f54 (Concat v_9274dd4 local__POST_i_lang) ) )
% v_9274dd4 := v_9274d34 ";\n$language = "
(assert (= v_9274dd4 (Concat v_9274d34 "_^sc^_^n^_^do^language") ) )
% v_9274d34 := v_9274bb4 local__POST_i_game
(assert (= v_9274d34 (Concat v_9274bb4 local__POST_i_game) ) )
% v_9274bb4 := v_9274b14 ";\n$game = "
(assert (= v_9274bb4 (Concat v_9274b14 "_^sc^_^n^_^do^game") ) )
% v_9274b14 := v_9274994 local__POST_i_book
(assert (= v_9274b14 (Concat v_9274994 local__POST_i_book) ) )
% v_9274994 := v_92748f4 ";\n$book = "
(assert (= v_9274994 (Concat v_92748f4 "_^sc^_^n^_^do^book") ) )
% v_92748f4 := v_9274774 local__POST_i_identica
(assert (= v_92748f4 (Concat v_9274774 local__POST_i_identica) ) )
% v_9274774 := v_92746d4 ";\n$identica = "
(assert (= v_9274774 (Concat v_92746d4 "_^sc^_^n^_^do^identica") ) )
% v_92746d4 := v_9274554 local__POST_i_twitter
(assert (= v_92746d4 (Concat v_9274554 local__POST_i_twitter) ) )
% v_9274554 := v_92744b4 ";\n$twitter = "
(assert (= v_9274554 (Concat v_92744b4 "_^sc^_^n^_^do^twitter") ) )
% v_92744b4 := v_9274334 local__POST_i_gravatar
(assert (= v_92744b4 (Concat v_9274334 local__POST_i_gravatar) ) )
% v_9274334 := v_9274294 ";\n$gravatar = "
(assert (= v_9274334 (Concat v_9274294 "_^sc^_^n^_^do^gravatar") ) )
% v_9274294 := v_9274114 local__POST_i_skin
(assert (= v_9274294 (Concat v_9274114 local__POST_i_skin) ) )
% v_9274114 := v_9274074 ";\n$skin = "
(assert (= v_9274114 (Concat v_9274074 "_^sc^_^n^_^do^skin") ) )
% v_9274074 := v_9273ef4 local__POST_i_author
(assert (= v_9274074 (Concat v_9273ef4 local__POST_i_author) ) )
% v_9273ef4 := v_9273e54 ";\n$author = "
(assert (= v_9273ef4 (Concat v_9273e54 "_^sc^_^n^_^do^author") ) )
% v_9273e54 := v_9273cd4 local__POST_i_id
(assert (= v_9273e54 (Concat v_9273cd4 local__POST_i_id) ) )
% v_9273cd4 := v_9273c34 ";\n$postid = "
(assert (= v_9273cd4 (Concat v_9273c34 "_^sc^_^n^_^do^postid") ) )
% v_9273c34 := v_9273ab4 local__POST_i_description
(assert (= v_9273c34 (Concat v_9273ab4 local__POST_i_description) ) )
% v_9273ab4 := v_9273a14 ";\n$description = "
(assert (= v_9273ab4 (Concat v_9273a14 "_^sc^_^n^_^do^description") ) )
% v_9273a14 := v_9273894 local__POST_i_title
(assert (= v_9273a14 (Concat v_9273894 local__POST_i_title) ) )
% v_9273894 := v_92737f4 ";\n$blogtitle = "
(assert (= v_9273894 (Concat v_92737f4 "_^sc^_^n^_^do^blogtitle") ) )
% v_92737f4 := v_9273674 local__POST_i_suri
(assert (= v_92737f4 (Concat v_9273674 local__POST_i_suri) ) )
% v_9273674 := v_92735d4 ";\n$suri = "
(assert (= v_9273674 (Concat v_92735d4 "_^sc^_^n^_^do^suri") ) )
% v_92735d4 := v_9273454 local__POST_i_uri
(assert (= v_92735d4 (Concat v_9273454 local__POST_i_uri) ) )
% v_9273454 := v_92733b4 ";\n$uri = "
(assert (= v_9273454 (Concat v_92733b4 "_^sc^_^n^_^do^uri") ) )
% v_92733b4 := "<?php $pass = " local__POST_i_pass
(assert (= v_92733b4 "<?php_^do^pass=" local__POST_i_pass) )
% local__POST_i_pass := zYh_aNyStR
% local__POST_i_uri := zYh_aNyStR
% local__POST_i_suri := zYh_aNyStR
% local__POST_i_title := zYh_aNyStR
% local__POST_i_description := zYh_aNyStR
% local__POST_i_id := zYh_aNyStR
% local__POST_i_author := zYh_aNyStR
% local__POST_i_skin := zYh_aNyStR
% local__POST_i_gravatar := zYh_aNyStR
% local__POST_i_twitter := zYh_aNyStR
% local__POST_i_identica := zYh_aNyStR
% local__POST_i_book := zYh_aNyStR
% local__POST_i_game := zYh_aNyStR
% local__POST_i_lang := zYh_aNyStR
% //===================================================================
% ==========================================================

(check-sat)
(get-model)

