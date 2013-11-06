(declare-variable	v_9e72fe4		bool)
(declare-variable	v_9e73078		bool)
(declare-variable	v_9e73114		bool)
(declare-variable	v_9e74e44		bool)
(declare-variable	v_9e74ed8		bool)
(declare-variable	v_9e750bc		bool)
(declare-variable	v_9e75204		bool)
(declare-variable	v_convertBool77		bool)
(declare-variable	v_phiBool129		bool)
(declare-variable	v_phiBool130		bool)
(declare-variable	v_phiBool131		bool)
(declare-variable	v_phiBool132		bool)
(declare-variable	v_phiBool133		bool)
(declare-variable	v_phiBool134		bool)
(declare-variable	v_phiBool135		bool)
%----------------------------------------
(declare-variable	T_arg_9e6c1d8		(_ BitVec 1) )
(declare-variable	T_arg_9e6c200		(_ BitVec 1) )
(declare-variable	T_arg_9e6c200_i_0bin00000000000000000000000000000000		(_ BitVec 1) )
(declare-variable	T_v_9e72c78		(_ BitVec 1) )
(declare-variable	T_v_9e72da8		(_ BitVec 1) )
(declare-variable	T_v_9e72e44		(_ BitVec 1) )
(declare-variable	T_v_9e72ee4		(_ BitVec 1) )
(declare-variable	T_v_9e72fe4		(_ BitVec 1) )
(declare-variable	T_v_9e74e44		(_ BitVec 1) )
(declare-variable	T_v_9e74f8c		(_ BitVec 1) )
(declare-variable	T_v_9e75020		(_ BitVec 1) )
(declare-variable	T_v_9e753cc		(_ BitVec 1) )
(declare-variable	T_v_9e7546c		(_ BitVec 1) )
(declare-variable	T_v_9e755cc		(_ BitVec 1) )
(declare-variable	T_v_9e7566c		(_ BitVec 1) )
(declare-variable	T_v_9e75728		(_ BitVec 1) )
(declare-variable	T_v_9e75858		(_ BitVec 1) )
(declare-variable	T_v_9e758dc		(_ BitVec 1) )
(declare-variable	T_v_9e78518		(_ BitVec 1) )
(declare-variable	T_v_9e785b4		(_ BitVec 1) )
(declare-variable	T_v_9e7886c		(_ BitVec 1) )
(declare-variable	T_v_9e78988		(_ BitVec 1) )
(declare-variable	T_v_9e7afbc		(_ BitVec 1) )
%----------------------------------------
(declare-variable	arg_9e6c200		Int)
(declare-variable	arg_9e6c200_i_0bin00000000000000000000000000000000		Int)
(declare-variable	v_9e75020		Int)
(declare-variable	v_9e7b050		Int)
%========================================

% ASSERT( v_9e74ed8 <=> v_9e74e44 );
(assert (=  v_9e74ed8  v_9e74e44  ) )
% ASSERT( T_v_9e74e44 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: method_exists()
(assert (=  T_v_9e74e44  #b0 ) )
% ASSERT( v_phiBool129 <=>  v_9e73114  );
(assert (=  v_phiBool129  v_9e73114  ) )
% ASSERT( T_v_9e78988 = IF v_phiBool129 THEN T_v_9e7886c ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_9e78988  (ite v_phiBool129 T_v_9e7886c #b0)  ) )
% ASSERT( v_phiBool130 <=>  v_phiBool131  );
(assert (=  v_phiBool130  v_phiBool131  ) )
% ASSERT( T_v_9e78988 = IF v_phiBool130 THEN T_v_9e72ee4 ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_9e78988  (ite v_phiBool130 T_v_9e72ee4 #b0)  ) )
% ASSERT( v_9e73114 <=> v_convertBool77 AND v_9e73078 );
(assert (=  v_9e73114   (and v_convertBool77 v_9e73078)   ) )
% ASSERT( T_v_9e72da8 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: get_class()
(assert (=  T_v_9e72da8  #b0  ) )
% ASSERT( T_arg_9e6c200_i_0bin00000000000000000000000000000000 = T_arg_9e6c200 );
(assert (=  T_arg_9e6c200_i_0bin00000000000000000000000000000000  T_arg_9e6c200  ) )
% ASSERT( v_9e73078 <=> NOT v_9e72fe4 );
(assert (=  v_9e73078  (not v_9e72fe4)  ) )
% ASSERT( T_v_9e72fe4 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: method_exists()
(assert (=  T_v_9e72fe4  #b0 ) )
% ASSERT( T_v_9e72ee4 = T_v_9e72e44 | T_v_9e72da8);
(assert (=  T_v_9e72ee4   (bvor T_v_9e72e44 T_v_9e72da8)   ) )
% ASSERT( T_v_9e72e44 = T_arg_9e6c1d8 | T_v_9e72c78);
(assert (=  T_v_9e72e44   (bvor T_arg_9e6c1d8 T_v_9e72c78)   ) )
% ASSERT( T_v_9e72c78 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: array_shift()
(assert (=  T_v_9e72c78  #b0 ) )
% ASSERT( T_v_9e7886c = T_v_9e785b4 | T_v_9e78518);
(assert (=  T_v_9e7886c   (bvor T_v_9e785b4 T_v_9e78518)   ) )
% ASSERT( T_v_9e785b4 = T_arg_9e6c1d8 | T_v_9e72c78);
(assert (=  T_v_9e785b4   (bvor T_arg_9e6c1d8 T_v_9e72c78)   ) )
% ASSERT( T_v_9e78518 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: get_parent_class()
(assert (=  T_v_9e78518  #b0 ) )
% ASSERT( T_v_9e7afbc = 0bin00000000000000000000000000000001 );
(assert (=  T_v_9e7afbc  #b1  ) )
% ASSERT( T_v_9e7afbc = 0bin00000000000000000000000000000000 | T_v_9e758dc);
(assert (=  T_v_9e7afbc   (bvor #b0 T_v_9e758dc)   ) )
% ASSERT( T_v_9e758dc = T_v_9e75858 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9e758dc   (bvor T_v_9e75858 #b0)   ) )
% ASSERT( v_phiBool132 <=>  v_9e750bc  AND  v_9e74ed8  );
(assert (=  v_phiBool132   (and v_9e750bc v_9e74ed8)   ) )
% ASSERT( T_v_9e75858 = IF v_phiBool132 THEN T_v_9e75728 ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_9e75858  (ite v_phiBool132 T_v_9e75728 #b0)  ) )
% ASSERT( v_phiBool133 <=>  v_9e74ed8  );
(assert (=  v_phiBool133  v_9e74ed8  ) )
% ASSERT( T_v_9e75858 = IF v_phiBool133 THEN T_v_9e74f8c ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_9e75858  (ite v_phiBool133 T_v_9e74f8c #b0)  ) )
% ASSERT( v_9e750bc <=> BVLT(0bin00000000000000000000000000000000,  v_9e75020) );
(assert (=  v_9e750bc (< 0  v_9e75020) ) )
% ASSERT( T_v_9e75020 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: count()
(assert (=  T_v_9e75020  #b0 ) )
% ASSERT( v_phiBool134 <=>  v_9e75204  AND  v_9e750bc  AND  v_9e74ed8  );
(assert (=  v_phiBool134   (and v_9e75204 (and v_9e750bc  v_9e74ed8 ) )   ) )
% ASSERT( T_v_9e75728 = IF v_phiBool134 THEN T_v_9e7546c ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_9e75728  (ite v_phiBool134 T_v_9e7546c #b0)  ) )
% ASSERT( v_phiBool135 <=>  ( NOT v_9e75204 )  AND  v_9e750bc  AND  v_9e74ed8  );
(assert (=  v_phiBool135   (and (not v_9e75204) (and v_9e750bc  v_9e74ed8 ) )   ) )
% ASSERT( T_v_9e75728 = IF v_phiBool135 THEN T_v_9e7566c ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_9e75728  (ite v_phiBool135 T_v_9e7566c #b0)  ) )
% ASSERT( v_9e75204 <=> (0bin00000000000000000000000000000000 = 0bin00000000000000000000000000000000) );
(assert (=  v_9e75204 (= 0 0 ) ) )
% ASSERT( T_v_9e7546c = T_v_9e74f8c | T_v_9e753cc);
(assert (=  T_v_9e7546c   (bvor T_v_9e74f8c T_v_9e753cc)   ) )
% ASSERT( T_v_9e74f8c = T_v_9e78988 | 0bin00000000000000000000000000000000);
(assert (=  T_v_9e74f8c   (bvor T_v_9e78988 #b0)   ) )
% ASSERT( T_v_9e753cc = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: php_sprintf()
(assert (=  T_v_9e753cc  #b0  ) )
% ASSERT( T_v_9e7566c = T_v_9e74f8c | T_v_9e755cc);
(assert (=  T_v_9e7566c   (bvor T_v_9e74f8c T_v_9e755cc)   ) )
% ASSERT( T_v_9e755cc = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: php_sprintf()
(assert (=  T_v_9e755cc  #b0  ) )
% ASSERT( v_9e74ed8 );
(assert v_9e74ed8 )

%========================================
(declare-variable	v_9e72da8		String)
(declare-variable	v_9e72ee4		String)
(declare-variable	v_9e72e44		String)
(declare-variable	arg_9e6c1d8		String)
(declare-variable	v_9e72c78		String)
(declare-variable	v_9e7886c		String)
(declare-variable	v_9e785b4		String)
(declare-variable	v_9e78518		String)
(declare-variable	v_9e7afbc		String)
(declare-variable	v_9e758dc		String)
(declare-variable	v_9e75858		String)
(declare-variable	v_9e7546c		String)
(declare-variable	v_9e74f8c		String)
(declare-variable	v_9e753cc		String)
(declare-variable	v_9e78988		String)
(declare-variable	v_9e7566c		String)
(declare-variable	v_9e755cc		String)
(declare-variable   v_9e75728       String)

% ----------------------------------------------------------
% //***** String CSTR =================================================
% v_phiBool129 | v_phiBool130 ? v_9e78988 := v_9e7886c | v_9e72ee4
(assert (=> v_phiBool129 (= v_9e78988 v_9e7886c) ) )
(assert (=> v_phiBool130 (= v_9e78988 v_9e72ee4) ) )
% v_convertBool77 := v_9e72da8 != ""
(assert (= v_convertBool77 (not (= v_9e72da8 "") ) ) )
% //[**] v_9e72da8 := get_class(arg_9e6c200_i_0bin00000000000000000000000000000000)
% v_9e72ee4 := v_9e72e44 v_9e72da8
(assert (= v_9e72ee4 (Concat v_9e72e44 v_9e72da8) ) )
% v_9e72e44 := arg_9e6c1d8 v_9e72c78
(assert (= v_9e72e44 (Concat arg_9e6c1d8 v_9e72c78) ) )
% //[**] v_9e72c78 := array_shift(arg_9e6c200)
% v_9e7886c := v_9e785b4 v_9e78518
(assert (= v_9e7886c (Concat v_9e785b4 v_9e78518) ) )
% v_9e785b4 := arg_9e6c1d8 v_9e72c78
(assert (= v_9e785b4 (Concat arg_9e6c1d8 v_9e72c78) ) )
% //[**] v_9e78518 := get_parent_class(v_9e72da8)
% v_9e7afbc := "$r = $this_>" v_9e758dc
(assert (= v_9e7afbc (Concat "_^do^r=_^do^this_>" v_9e758dc ) ) )
% v_9e758dc := v_9e75858 ");"
(assert (= v_9e758dc (Concat v_9e75858 "_^sc^") ) )
% v_phiBool132 | v_phiBool133 ? v_9e75858 := v_9e75728 | v_9e74f8c
(assert (=> v_phiBool132 (= v_9e75858 v_9e75728) ) )
(assert (=> v_phiBool133 (= v_9e75858 v_9e74f8c) ) )
% v_phiBool134 | v_phiBool135 ? v_9e75728 := v_9e7546c | v_9e7566c
(assert (=> v_phiBool134 (= v_9e75728 v_9e7546c) ) )
(assert (=> v_phiBool135 (= v_9e75728 v_9e7566c) ) )
% v_9e7546c := v_9e74f8c v_9e753cc
(assert (= v_9e7546c (Concat v_9e74f8c v_9e753cc) ) )
% v_9e74f8c := v_9e78988 "("
(assert (= v_9e74f8c (Concat v_9e78988 "") ) )
% //[**] v_9e753cc := php_sprintf("$args[%s]", 0bin00000000000000000000000000000000)
% v_9e7566c := v_9e74f8c v_9e755cc
(assert (= v_9e7566c (Concat v_9e74f8c v_9e755cc) ) )
% //[**] v_9e755cc := php_sprintf(",$args[%s]", 0bin00000000000000000000000000000000)
% ==========================================================

(check-sat)
(get-model)

