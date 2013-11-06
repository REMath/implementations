(declare-variable	v_9f8ab6c		String)
(declare-variable	v_9f8ac00		String)
(declare-variable	v_9f9cb6c		bool)
(declare-variable	v_fileNameBool0		bool)
%----------------------------------------
(declare-variable	T_local__POST		(_ BitVec 1) )
(declare-variable	T_local__POST_i_author		(_ BitVec 1) )
(declare-variable	T_local__POST_i_blog		(_ BitVec 1) )
(declare-variable	T_local__POST_i_post		(_ BitVec 1) )
(declare-variable	T_local__POST_i_title		(_ BitVec 1) )
(declare-variable	T_local__POST_i_type		(_ BitVec 1) )
(declare-variable	T_v_9f8a990		(_ BitVec 1) )
(declare-variable	T_v_9f8aa2c		(_ BitVec 1) )
(declare-variable	T_v_9f8aacc		(_ BitVec 1) )
(declare-variable	T_v_9fa12fc		(_ BitVec 1) )
(declare-variable	T_v_9fa139c		(_ BitVec 1) )
(declare-variable	T_v_9fa151c		(_ BitVec 1) )
(declare-variable	T_v_9fa15bc		(_ BitVec 1) )
(declare-variable	T_v_9fa173c		(_ BitVec 1) )
(declare-variable	T_v_9fa17dc		(_ BitVec 1) )
(declare-variable	T_v_9fa187c		(_ BitVec 1) )
(declare-variable	T_v_9fa191c		(_ BitVec 1) )
(declare-variable	T_v_9fa19b0		(_ BitVec 1) )
(declare-variable	T_v_9fa1a40		(_ BitVec 1) )
(declare-variable	T_v_9fa1adc		(_ BitVec 1) )
(declare-variable	T_v_9fa1b7c		(_ BitVec 1) )
(declare-variable	T_v_9fa1c10		(_ BitVec 1) )
(declare-variable	T_v_9fa1ca0		(_ BitVec 1) )
(declare-variable	T_v_9fa1d3c		(_ BitVec 1) )
(declare-variable	T_v_9fa1ddc		(_ BitVec 1) )
(declare-variable	T_v_9fa1e70		(_ BitVec 1) )
(declare-variable	T_v_9fa1f00		(_ BitVec 1) )
(declare-variable	T_v_9fa1f9c		(_ BitVec 1) )
(declare-variable	T_v_9fa203c		(_ BitVec 1) )
(declare-variable	T_v_9fa20d0		(_ BitVec 1) )
(declare-variable	T_v_9fa216c		(_ BitVec 1) )
(declare-variable	T_v_9fa220c		(_ BitVec 1) )
(declare-variable	T_v_9fa238c		(_ BitVec 1) )
(declare-variable	T_v_9fa242c		(_ BitVec 1) )
%----------------------------------------
(declare-variable	local__POST		Int)
(declare-variable	v_9fa24cc		Int)
%========================================

% ASSERT( T_local__POST_i_post = T_local__POST );
(assert (=  T_local__POST_i_post  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( v_9f8ac00 <=> v_9f8ab6c );
(assert (=  v_9f8ac00  v_9f8ab6c  ) )
% ASSERT( T_v_9f8aacc = T_v_9f8aa2c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9f8aacc   (bvor T_v_9f8aa2c #b0)   ) )
% ASSERT( T_v_9f8aa2c = 0bin00000000000000000000000000000000 | T_v_9f8a990);
(assert (=  T_v_9f8aa2c   (bvor #b0 T_v_9f8a990)   ) )
% ASSERT( T_v_9f8a990 = 0bin00000000000000000000000000000000);
(assert (=  T_v_9f8a990  #b0  ) )
% ASSERT( T_v_9fa242c = 0bin00000000000000000000000000000001 );
(assert (=  T_v_9fa242c  #b1  ) )
% ASSERT( v_fileNameBool0 );
(assert v_fileNameBool0 )
% ASSERT( T_v_9fa242c = T_v_9fa238c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa242c   (bvor T_v_9fa238c #b0)   ) )
% ASSERT( T_v_9fa238c = T_v_9fa220c | T_local__POST_i_blog);
(assert (=  T_v_9fa238c   (bvor T_v_9fa220c T_local__POST_i_blog)   ) )
% ASSERT( T_v_9fa220c = T_v_9fa216c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa220c   (bvor T_v_9fa216c #b0)   ) )
% ASSERT( T_v_9fa216c = T_v_9fa203c | T_v_9fa20d0);
(assert (=  T_v_9fa216c   (bvor T_v_9fa203c T_v_9fa20d0)   ) )
% ASSERT( T_v_9fa203c = T_v_9fa1f9c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa203c   (bvor T_v_9fa1f9c #b0)   ) )
% ASSERT( T_v_9fa1f9c = T_v_9fa1ddc | T_v_9fa1f00);
(assert (=  T_v_9fa1f9c   (bvor T_v_9fa1ddc T_v_9fa1f00)   ) )
% ASSERT( T_v_9fa1ddc = T_v_9fa1d3c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa1ddc   (bvor T_v_9fa1d3c #b0)   ) )
% ASSERT( T_v_9fa1d3c = T_v_9fa1b7c | T_v_9fa1ca0);
(assert (=  T_v_9fa1d3c   (bvor T_v_9fa1b7c T_v_9fa1ca0)   ) )
% ASSERT( T_v_9fa1b7c = T_v_9fa1adc | 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa1b7c   (bvor T_v_9fa1adc #b0)   ) )
% ASSERT( T_v_9fa1adc = T_v_9fa191c | T_v_9fa1a40);
(assert (=  T_v_9fa1adc   (bvor T_v_9fa191c T_v_9fa1a40)   ) )
% ASSERT( T_v_9fa191c = T_v_9fa187c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa191c   (bvor T_v_9fa187c #b0)   ) )
% ASSERT( T_v_9fa187c = T_v_9fa17dc | 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa187c   (bvor T_v_9fa17dc #b0)   ) )
% ASSERT( T_v_9fa17dc = T_v_9fa173c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa17dc   (bvor T_v_9fa173c #b0)   ) )
% ASSERT( T_v_9fa173c = T_v_9fa15bc | T_local__POST_i_type);
(assert (=  T_v_9fa173c   (bvor T_v_9fa15bc T_local__POST_i_type)   ) )
% ASSERT( T_v_9fa15bc = T_v_9fa151c | 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa15bc   (bvor T_v_9fa151c #b0)   ) )
% ASSERT( T_v_9fa151c = T_v_9fa139c | T_local__POST_i_author);
(assert (=  T_v_9fa151c   (bvor T_v_9fa139c T_local__POST_i_author)   ) )
% ASSERT( T_v_9fa139c = T_v_9fa12fc | 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa139c   (bvor T_v_9fa12fc #b0)   ) )
% ASSERT( T_v_9fa12fc = 0bin00000000000000000000000000000000 | T_local__POST_i_title);
(assert (=  T_v_9fa12fc   (bvor #b0 T_local__POST_i_title)   ) )
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
% ASSERT( T_v_9fa1a40 = T_v_9fa19b0);
(assert (=  T_v_9fa1a40  T_v_9fa19b0  ) )
% ASSERT( T_v_9fa19b0 = 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa19b0  #b0  ) )
% ASSERT( T_v_9fa1ca0 = T_v_9fa1c10);
(assert (=  T_v_9fa1ca0  T_v_9fa1c10  ) )
% ASSERT( T_v_9fa1c10 = 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa1c10  #b0  ) )
% ASSERT( T_v_9fa1f00 = T_v_9fa1e70);
(assert (=  T_v_9fa1f00  T_v_9fa1e70  ) )
% ASSERT( T_v_9fa1e70 = 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa1e70  #b0  ) )
% ASSERT( T_v_9fa20d0 = 0bin00000000000000000000000000000000);
(assert (=  T_v_9fa20d0  #b0  ) )
% ASSERT( T_local__POST_i_blog = T_local__POST );
(assert (=  T_local__POST_i_blog  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )

%========================================
(declare-variable	local__POST_i_post		String)
(declare-variable   v_9f8aacc       String)
(declare-variable   local__POST_i_title       String)
(declare-variable	v_9f8aa2c		String)
(declare-variable	v_9f8a990		String)
(declare-variable	v_fileName0		String)
(declare-variable	v_9fa242c		String)
(declare-variable	v_9fa238c		String)
(declare-variable	v_9fa220c		String)
(declare-variable	local__POST_i_blog		String)
(declare-variable	v_9fa216c		String)
(declare-variable	v_9fa203c		String)
(declare-variable	v_9fa20d0		String)
(declare-variable	v_9fa1f9c		String)
(declare-variable	v_9fa1ddc		String)
(declare-variable	v_9fa1f00		String)
(declare-variable	v_9fa1d3c		String)
(declare-variable	v_9fa1b7c		String)
(declare-variable	v_9fa1ca0		String)
(declare-variable	v_9fa1adc		String)
(declare-variable	v_9fa191c		String)
(declare-variable	v_9fa1a40		String)
(declare-variable	v_9fa187c		String)
(declare-variable	v_9fa17dc		String)
(declare-variable	v_9fa173c		String)
(declare-variable	v_9fa15bc		String)
(declare-variable	local__POST_i_type		String)
(declare-variable	v_9fa151c		String)
(declare-variable	v_9fa139c		String)
(declare-variable	local__POST_i_author		String)
(declare-variable	v_9fa12fc		String)
(declare-variable	v_9fa19b0		String)
(declare-variable	v_9fa1c10		String)
(declare-variable	v_9fa1e70		String)
(declare-variable   tmp       String)
% ----------------------------------------------------------
% v_9f9cb6c := local__POST_i_post == "write"
(assert (= v_9f9cb6c (= local__POST_i_post "write") ) )
% local__POST_i_post := zYh_aNyStR
% v_9f8ab6c := v_9f8aacc
(assert (= v_9f8ab6c v_9f8aacc) )
% v_9f8aacc := v_9f8aa2c ".txt"
(assert (= v_9f8aacc (Concat v_9f8aa2c ".txt") ) )
% v_9f8aa2c := "data/posts/" v_9f8a990
(assert (= v_9f8aa2c "data/posts/" v_9f8a990) )
% v_9f8a990 := "Y_m_d_H_i_s"
(assert (= v_9f8a990 "Y_m_d_H_i_s") )
% v_fileName0 := zYh_aNyStR ".php"
% v_fileNameBool0 := v_9f8ab6c == v_fileName0
(assert (= v_fileName0 (Concat tmp ".php") ) )
(assert (= v_fileNameBool0 (= v_9f8ab6c v_fileName0) ) )
% v_9fa242c := v_9fa238c ";?>"
(assert (= v_9fa242c (Concat v_9fa238c "_^sc^?>") ) )
% v_9fa238c := v_9fa220c local__POST_i_blog
(assert (= v_9fa238c (Concat v_9fa220c local__POST_i_blog) ) )
% v_9fa220c := v_9fa216c ";\n$post = "
(assert (= v_9fa220c (Concat v_9fa216c "_^sc^_^n^_^do^post") ) )
% v_9fa216c := v_9fa203c v_9fa20d0
(assert (= v_9fa216c (Concat v_9fa203c v_9fa20d0) ) )
% v_9fa203c := v_9fa1f9c ";\n$pubDate = "
(assert (= v_9fa203c (Concat v_9fa1f9c "_^sc^_^n^_^do^pubDate") ) )
% v_9fa1f9c := v_9fa1ddc v_9fa1f00
(assert (= v_9fa1f9c (Concat v_9fa1ddc v_9fa1f00) ) )
% v_9fa1ddc := v_9fa1d3c ";\n$dy = "
(assert (= v_9fa1ddc (Concat v_9fa1d3c "_^sc^_^n^_^do^dy") ) )
% v_9fa1d3c := v_9fa1b7c v_9fa1ca0
(assert (= v_9fa1d3c (Concat v_9fa1b7c v_9fa1ca0) ) )
% v_9fa1b7c := v_9fa1adc ";\n$dd = "
(assert (= v_9fa1b7c (Concat v_9fa1adc "_^sc^_^n^_^do^dd") ) )
% v_9fa1adc := v_9fa191c v_9fa1a40
(assert (= v_9fa1adc (Concat v_9fa191c v_9fa1a40) ) )
% v_9fa191c := v_9fa187c ";\n$dm = "
(assert (= v_9fa191c (Concat v_9fa187c "_^sc^_^n^_^do^dm") ) )
% v_9fa187c := v_9fa17dc "3"
(assert (= v_9fa187c (Concat v_9fa17dc "3") ) )
% v_9fa17dc := v_9fa173c ";\n$id = "
(assert (= v_9fa17dc (Concat v_9fa173c "_^sc^_^n^_^do^id") ) )
% v_9fa173c := v_9fa15bc local__POST_i_type
(assert (= v_9fa173c (Concat v_9fa15bc local__POST_i_type) ) )
% v_9fa15bc := v_9fa151c ";\n$type = "
(assert (= v_9fa15bc (Concat v_9fa151c "_^sc^_^n^_^do^type") ) )
% v_9fa151c := v_9fa139c local__POST_i_author
(assert (= v_9fa151c (Concat v_9fa139c local__POST_i_author) ) )
% v_9fa139c := v_9fa12fc ";\n$author = "
(assert (= v_9fa139c (Concat v_9fa12fc "_^sc^_^n^_^do^author") ) )
% v_9fa12fc := "<?php\n$title = " local__POST_i_title
(assert (= v_9fa12fc "<?php_^n^_^do^title=" local__POST_i_title) )
% local__POST_i_title := zYh_aNyStR
% local__POST_i_author := zYh_aNyStR
% local__POST_i_type := zYh_aNyStR
% v_9fa1a40 := v_9fa19b0
(assert (= v_9fa1a40 v_9fa19b0) )
% v_9fa19b0 := zYh_aNyStR
% v_9fa1ca0 := v_9fa1c10
(assert (= v_9fa1ca0 v_9fa1c10) )
% v_9fa1c10 := zYh_aNyStR
% v_9fa1f00 := v_9fa1e70
(assert (= v_9fa1f00 v_9fa1e70) )
% v_9fa1e70 := zYh_aNyStR
% v_9fa20d0 := "D, d M Y H:i O"
(assert (= v_9fa20d0 "D_d_M_Y_H_i_O") )
% local__POST_i_blog := zYh_aNyStR
% //===================================================================
% ==========================================================

(check-sat)
(get-model)

