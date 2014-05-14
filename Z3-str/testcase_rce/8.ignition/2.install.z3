(declare-variable	v_9b1e424		bool)
(declare-variable	v_9b1f9bc		bool)
(declare-variable	v_9b1fa50		bool)
%----------------------------------------
(declare-variable	T_local__POST		(_ BitVec 1) )
(declare-variable	T_local__POST_i_author		(_ BitVec 1) )
(declare-variable	T_local__POST_i_pass		(_ BitVec 1) )
(declare-variable	T_local__POST_i_title		(_ BitVec 1) )
(declare-variable	T_local__POST_i_uri		(_ BitVec 1) )
(declare-variable	T_v_9b1fbd8		(_ BitVec 1) )
(declare-variable	T_v_9b1fc74		(_ BitVec 1) )
(declare-variable	T_v_9b1fd14		(_ BitVec 1) )
(declare-variable	T_v_9b1fe94		(_ BitVec 1) )
(declare-variable	T_v_9b1ff34		(_ BitVec 1) )
(declare-variable	T_v_9b200b4		(_ BitVec 1) )
(declare-variable	T_v_9b20154		(_ BitVec 1) )
(declare-variable	T_v_9b202d4		(_ BitVec 1) )
(declare-variable	T_v_9b20374		(_ BitVec 1) )
(declare-variable	T_v_9b204f4		(_ BitVec 1) )
(declare-variable	T_v_9b20594		(_ BitVec 1) )
%----------------------------------------
(declare-variable	local__POST		Int)
(declare-variable	v_9b20634		Int)
%========================================

% ASSERT( v_9b1e424 <=> FALSE );
(assert (=  v_9b1e424  false  ) )
% ASSERT( T_local__POST_i_pass = T_local__POST );
(assert (=  T_local__POST_i_pass  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( v_9b1fa50 <=> v_9b1f9bc );
(assert (=  v_9b1fa50  v_9b1f9bc  ) )
% ASSERT( T_v_9b20594 = 0bin00000000000000000000000000000001 );
(assert (=  T_v_9b20594  #b1  ) )
% ASSERT( T_v_9b20594 = T_v_9b204f4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9b20594   (bvor T_v_9b204f4 #b0)   ) )
% ASSERT( T_v_9b204f4 = T_v_9b20374 | T_local__POST_i_author);
(assert (=  T_v_9b204f4   (bvor T_v_9b20374 T_local__POST_i_author)   ) )
% ASSERT( T_v_9b20374 = T_v_9b202d4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9b20374   (bvor T_v_9b202d4 #b0)   ) )
% ASSERT( T_v_9b202d4 = T_v_9b20154 | T_local__POST_i_title);
(assert (=  T_v_9b202d4   (bvor T_v_9b20154 T_local__POST_i_title)   ) )
% ASSERT( T_v_9b20154 = T_v_9b200b4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9b20154   (bvor T_v_9b200b4 #b0)   ) )
% ASSERT( T_v_9b200b4 = T_v_9b1ff34 | T_local__POST_i_uri);
(assert (=  T_v_9b200b4   (bvor T_v_9b1ff34 T_local__POST_i_uri)   ) )
% ASSERT( T_v_9b1ff34 = T_v_9b1fe94 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9b1ff34   (bvor T_v_9b1fe94 #b0)   ) )
% ASSERT( T_v_9b1fe94 = T_v_9b1fd14 | T_local__POST_i_uri);
(assert (=  T_v_9b1fe94   (bvor T_v_9b1fd14 T_local__POST_i_uri)   ) )
% ASSERT( T_v_9b1fd14 = T_v_9b1fc74 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9b1fd14   (bvor T_v_9b1fc74 #b0)   ) )
% ASSERT( T_v_9b1fc74 = 0bin00000000000000000000000000000000 | T_v_9b1fbd8);
(assert (=  T_v_9b1fc74   (bvor #b0 T_v_9b1fbd8)   ) )
% ASSERT( T_local__POST_i_pass = T_local__POST );
(assert (=  T_local__POST_i_pass  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_uri = T_local__POST );
(assert (=  T_local__POST_i_uri  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_uri = T_local__POST );
(assert (=  T_local__POST_i_uri  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_title = T_local__POST );
(assert (=  T_local__POST_i_title  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_author = T_local__POST );
(assert (=  T_local__POST_i_author  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( NOT v_9b1e424 );
(assert (not v_9b1e424) )
% ASSERT( v_9b1fa50 );
(assert v_9b1fa50 )

%========================================
(declare-variable	v_9b20594		String)
(declare-variable	v_9b204f4		String)
(declare-variable	v_9b20374		String)
(declare-variable	local__POST_i_author		String)
(declare-variable	v_9b202d4		String)
(declare-variable	v_9b20154		String)
(declare-variable	local__POST_i_title		String)
(declare-variable	v_9b200b4		String)
(declare-variable	v_9b1ff34		String)
(declare-variable	local__POST_i_uri		String)
(declare-variable	v_9b1fe94		String)
(declare-variable	v_9b1fd14		String)
(declare-variable	v_9b1fc74		String)
(declare-variable   tmp       String)
(declare-variable   name       String)
(declare-variable   v_9b1fbd8       String)

% ----------------------------------------------------------
% local__POST_i_pass := zYh_aNyStR
% v_9b1f9bc := "data/settings.php"
(assert (= name (Concat tmp ".php") ) )
(assert (= v_9b1f9bc (= name "data/settings.php") ) )
% v_9b20594 := v_9b204f4 ";\n$skin = default;\n\nrequire_once(template.php);\nrequire_once(lang/en.php); "
(assert (= v_9b20594 (Concat v_9b204f4 "_^sc^_^n^_^do^skin") ) )
% v_9b204f4 := v_9b20374 local__POST_i_author
(assert (= v_9b204f4 (Concat v_9b20374 local__POST_i_author) ) )
% v_9b20374 := v_9b202d4 ";\n$description = Just another sad excuse for a blog; \n$postid = 2;\n$author = "
(assert (= v_9b20374 (Concat v_9b202d4 "_^sc^_^n^_^do^description") ) )
% v_9b202d4 := v_9b20154 local__POST_i_title
(assert (= v_9b202d4 (Concat v_9b20154 local__POST_i_title) ) )
% v_9b20154 := v_9b200b4 ";\n$blogtitle = "
(assert (= v_9b20154 (Concat v_9b200b4 "_^sc^_^n^_^do^blogtitle") ) )
% v_9b200b4 := v_9b1ff34 local__POST_i_uri
(assert (= v_9b200b4 (Concat v_9b1ff34 local__POST_i_uri) ) )
% v_9b1ff34 := v_9b1fe94 ";\n$suri = "
(assert (= v_9b1ff34 (Concat v_9b1fe94 "_^sc^_^n^_^do^suri") ) )
% v_9b1fe94 := v_9b1fd14 local__POST_i_uri
(assert (= v_9b1fe94 (Concat v_9b1fd14 local__POST_i_uri) ) )
% v_9b1fd14 := v_9b1fc74 ";\n$uri = "
(assert (= v_9b1fd14 (Concat v_9b1fc74 "_^sc^_^n^_^do^uri") ) )
% v_9b1fc74 := "<?php $pass = " v_9b1fbd8
(assert (= v_9b1fc74 "<?php_^do^pass=" v_9b1fbd8) )
% local__POST_i_uri := zYh_aNyStR
% local__POST_i_title := zYh_aNyStR
% local__POST_i_author := zYh_aNyStR
% //===================================================================
% ==========================================================

(check-sat)
(get-model)

