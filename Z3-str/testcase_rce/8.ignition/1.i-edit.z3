(declare-variable	v_9cf0c74		bool)
(declare-variable	v_9cf2bd4		bool)
(declare-variable	v_9cf2c68		bool)
%----------------------------------------
(declare-variable	T_local__POST		(_ BitVec 1) )
(declare-variable	T_local__POST_i_author		(_ BitVec 1) )
(declare-variable	T_local__POST_i_blog		(_ BitVec 1) )
(declare-variable	T_local__POST_i_edit		(_ BitVec 1) )
(declare-variable	T_local__POST_i_post		(_ BitVec 1) )
(declare-variable	T_local__POST_i_title		(_ BitVec 1) )
(declare-variable	T_local__POST_i_type		(_ BitVec 1) )
(declare-variable	T_v_9cbd818		(_ BitVec 1) )
(declare-variable	T_v_9cf2dfc		(_ BitVec 1) )
(declare-variable	T_v_9cf2e9c		(_ BitVec 1) )
(declare-variable	T_v_9cf301c		(_ BitVec 1) )
(declare-variable	T_v_9cf30bc		(_ BitVec 1) )
(declare-variable	T_v_9cf323c		(_ BitVec 1) )
(declare-variable	T_v_9cf32dc		(_ BitVec 1) )
(declare-variable	T_v_9cf337c		(_ BitVec 1) )
(declare-variable	T_v_9cf341c		(_ BitVec 1) )
(declare-variable	T_v_9cf34bc		(_ BitVec 1) )
(declare-variable	T_v_9cf355c		(_ BitVec 1) )
(declare-variable	T_v_9cf35fc		(_ BitVec 1) )
(declare-variable	T_v_9cf369c		(_ BitVec 1) )
(declare-variable	T_v_9cf373c		(_ BitVec 1) )
(declare-variable	T_v_9cf37dc		(_ BitVec 1) )
(declare-variable	T_v_9cf387c		(_ BitVec 1) )
(declare-variable	T_v_9cf391c		(_ BitVec 1) )
(declare-variable	T_v_9cf3a9c		(_ BitVec 1) )
(declare-variable	T_v_9cf3b3c		(_ BitVec 1) )
%----------------------------------------
(declare-variable	local__POST		Int)
(declare-variable	v_9cf3bdc		Int)
%========================================

% ASSERT( T_local__POST_i_post = T_local__POST );
(assert (=  T_local__POST_i_post  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( v_9cf2c68 <=> v_9cf2bd4 );
(assert (=  v_9cf2c68  v_9cf2bd4  ) )
% ASSERT( T_local__POST_i_edit = T_local__POST );
(assert (=  T_local__POST_i_edit  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_v_9cf3b3c = 0bin00000000000000000000000000000001 );
(assert (=  T_v_9cf3b3c  #b1  ) )
% ASSERT( T_v_9cf3b3c = T_v_9cf3a9c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9cf3b3c   (bvor T_v_9cf3a9c #b0)   ) )
% ASSERT( T_v_9cf3a9c = T_v_9cf391c | T_local__POST_i_blog);
(assert (=  T_v_9cf3a9c   (bvor T_v_9cf391c T_local__POST_i_blog)   ) )
% ASSERT( T_v_9cf391c = T_v_9cf387c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9cf391c   (bvor T_v_9cf387c #b0)   ) )
% ASSERT( T_v_9cf387c = T_v_9cf37dc | T_v_9cbd818);
(assert (=  T_v_9cf387c   (bvor T_v_9cf37dc T_v_9cbd818)   ) )
% ASSERT( T_v_9cf37dc = T_v_9cf373c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9cf37dc   (bvor T_v_9cf373c #b0)   ) )
% ASSERT( T_v_9cf373c = T_v_9cf369c | T_v_9cbd818);
(assert (=  T_v_9cf373c   (bvor T_v_9cf369c T_v_9cbd818)   ) )
% ASSERT( T_v_9cf369c = T_v_9cf35fc | 0bin00000000000000000000000000000000);
(assert (=  T_v_9cf369c   (bvor T_v_9cf35fc #b0)   ) )
% ASSERT( T_v_9cf35fc = T_v_9cf355c | T_v_9cbd818);
(assert (=  T_v_9cf35fc   (bvor T_v_9cf355c T_v_9cbd818)   ) )
% ASSERT( T_v_9cf355c = T_v_9cf34bc | 0bin00000000000000000000000000000000);
(assert (=  T_v_9cf355c   (bvor T_v_9cf34bc #b0)   ) )
% ASSERT( T_v_9cf34bc = T_v_9cf341c | T_v_9cbd818);
(assert (=  T_v_9cf34bc   (bvor T_v_9cf341c T_v_9cbd818)   ) )
% ASSERT( T_v_9cf341c = T_v_9cf337c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9cf341c   (bvor T_v_9cf337c #b0)   ) )
% ASSERT( T_v_9cf337c = T_v_9cf32dc | T_v_9cbd818);
(assert (=  T_v_9cf337c   (bvor T_v_9cf32dc T_v_9cbd818)   ) )
% ASSERT( T_v_9cf32dc = T_v_9cf323c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9cf32dc   (bvor T_v_9cf323c #b0)   ) )
% ASSERT( T_v_9cf323c = T_v_9cf30bc | T_local__POST_i_type);
(assert (=  T_v_9cf323c   (bvor T_v_9cf30bc T_local__POST_i_type)   ) )
% ASSERT( T_v_9cf30bc = T_v_9cf301c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9cf30bc   (bvor T_v_9cf301c #b0)   ) )
% ASSERT( T_v_9cf301c = T_v_9cf2e9c | T_local__POST_i_author);
(assert (=  T_v_9cf301c   (bvor T_v_9cf2e9c T_local__POST_i_author)   ) )
% ASSERT( T_v_9cf2e9c = T_v_9cf2dfc | 0bin00000000000000000000000000000000);
(assert (=  T_v_9cf2e9c   (bvor T_v_9cf2dfc #b0)   ) )
% ASSERT( T_v_9cf2dfc = 0bin00000000000000000000000000000000 | T_local__POST_i_title);
(assert (=  T_v_9cf2dfc   (bvor #b0 T_local__POST_i_title)   ) )
% ASSERT( T_local__POST_i_title = T_local__POST );
(assert (=  T_local__POST_i_title  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_author = T_local__POST );
(assert (=  T_local__POST_i_author  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_type = T_local__POST );
(assert (=  T_local__POST_i_type  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_blog = T_local__POST );
(assert (=  T_local__POST_i_blog  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( v_9cf0c74 );
(assert v_9cf0c74 )
% ASSERT( v_9cf2c68 );
(assert v_9cf2c68 )

%========================================
(declare-variable	local__POST_i_post		String)
(declare-variable	local__POST_i_edit		String)
(declare-variable   local__POST_i_title      String)
(declare-variable	v_9cf3b3c		String)
(declare-variable	v_9cf3a9c		String)
(declare-variable	v_9cf391c		String)
(declare-variable	local__POST_i_blog		String)
(declare-variable	v_9cf387c		String)
(declare-variable	v_9cf37dc		String)
(declare-variable	v_9cf373c		String)
(declare-variable	v_9cf369c		String)
(declare-variable	v_9cf35fc		String)
(declare-variable	v_9cf355c		String)
(declare-variable	v_9cf34bc		String)
(declare-variable	v_9cf341c		String)
(declare-variable	v_9cf337c		String)
(declare-variable	v_9cf32dc		String)
(declare-variable	v_9cf323c		String)
(declare-variable	v_9cf30bc		String)
(declare-variable	local__POST_i_type		String)
(declare-variable	v_9cf301c		String)
(declare-variable	v_9cf2e9c		String)
(declare-variable	local__POST_i_author		String)
(declare-variable	v_9cf2dfc		String)
% ----------------------------------------------------------
% v_9cf0c74 := local__POST_i_post == "write"
(assert (= v_9cf0c74 (= local__POST_i_post "write") ) )
% local__POST_i_post := zYh_aNyStR
% v_9cf2bd4 := local__POST_i_edit
(assert (= v_9cf2bd4 (not (= local__POST_i_edit "") ) ) )
% local__POST_i_edit := zYh_aNyStR
% v_9cf3b3c := v_9cf3a9c "\";"
(assert (= v_9cf3b3c (Concat v_9cf3a9c "_^sc^") ) )
% v_9cf3a9c := v_9cf391c local__POST_i_blog
(assert (= v_9cf3a9c (Concat v_9cf391c local__POST_i_blog) ) )
% v_9cf391c := v_9cf387c "\";\r\n    $post = \""
(assert (= v_9cf391c (Concat v_9cf387c "_^sc^_^n^post=") ) )
% v_9cf387c := v_9cf37dc
(assert (= v_9cf387c v_9cf37dc) )
% v_9cf37dc := v_9cf373c "\";\r\n    $pubDate = \""
(assert (= v_9cf37dc (Concat v_9cf373c "_^sc^_^n^pubDate=") ) )
% v_9cf373c := v_9cf369c
(assert (= v_9cf373c v_9cf369c) )
% v_9cf369c := v_9cf35fc "\";\r\n    $dy = \""
(assert (= v_9cf369c (Concat v_9cf35fc "_^sc^_^n^dy=") ) )
% v_9cf35fc := v_9cf355c
(assert (= v_9cf35fc v_9cf355c) )
% v_9cf355c := v_9cf34bc "\";\r\n    $dd = \""
(assert (= v_9cf355c (Concat v_9cf34bc "_^sc^_^n^dd=") ) )
% v_9cf34bc := v_9cf341c
(assert (= v_9cf34bc v_9cf341c) )
% v_9cf341c := v_9cf337c "\";\r\n    $dm = \""
(assert (= v_9cf341c (Concat v_9cf337c "_^sc^_^n^dm=") ) )
% v_9cf337c := v_9cf32dc
(assert (= v_9cf337c v_9cf32dc) )
% v_9cf32dc := v_9cf323c "\";\r\n    $id = \""
(assert (= v_9cf32dc (Concat v_9cf323c "_^sc^_^n^id=") ) )
% v_9cf323c := v_9cf30bc local__POST_i_type
(assert (= v_9cf323c (Concat v_9cf30bc local__POST_i_type) ) )
% v_9cf30bc := v_9cf301c "\";\r\n    $type = \""
(assert (= v_9cf30bc (Concat v_9cf301c "_^sc^_^n^type=") ) )
% v_9cf301c := v_9cf2e9c local__POST_i_author
(assert (= v_9cf301c (Concat v_9cf2e9c local__POST_i_author) ) )
% v_9cf2e9c := v_9cf2dfc "\";\r\n    $author = \""
(assert (= v_9cf2e9c (Concat v_9cf2dfc "_^sc^_^n^author=") ) )
% v_9cf2dfc := "<?php\r\n    $title = \"" local__POST_i_title
(assert (= v_9cf2dfc "<?php_^r_^n^_^do^title_=_" local__POST_i_title) )
% local__POST_i_title := zYh_aNyStR
% local__POST_i_author := zYh_aNyStR
% local__POST_i_type := zYh_aNyStR
% local__POST_i_blog := zYh_aNyStR
% //===================================================================
% ==========================================================

(check-sat)
(get-model)

