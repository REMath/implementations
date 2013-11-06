(declare-variable	v_a6165e4		bool)
(declare-variable	v_a6208dc		bool)
(declare-variable	v_a6211b4		bool)
(declare-variable	v_a62139c		bool)
(declare-variable	v_a6214dc		bool)
(declare-variable	v_a62157c		bool)
(declare-variable	v_a633c60		bool)
(declare-variable	v_a62f220		bool)
(declare-variable	v_a62f6e8		bool)
(declare-variable	v_a62f778		bool)
(declare-variable	v_a62fb10		bool)
(declare-variable	v_a62fba0		bool)
(declare-variable	v_a633168		bool)
(declare-variable	v_a6331f8		bool)
(declare-variable	v_a63350c		bool)
(declare-variable	v_a633838		bool)
(declare-variable	v_a6338c8		bool)
(declare-variable	v_convertBool88		bool)
(declare-variable	v_convertBool89		bool)
(declare-variable	v_convertBool90		bool)
(declare-variable	v_convertBool91		bool)
(declare-variable	v_convertBool92		bool)
(declare-variable	v_phiBool180		bool)
(declare-variable	v_phiBool181		bool)
(declare-variable	v_phiBool182		bool)
(declare-variable	v_phiBool183		bool)
(declare-variable	v_phiBool184		bool)
(declare-variable	v_phiBool185		bool)
(declare-variable	v_phiBool186		bool)
(declare-variable	v_phiBool187		bool)
(declare-variable	v_phiBool188		bool)
(declare-variable	v_phiBool189		bool)
(declare-variable	v_phiBool190		bool)
(declare-variable	v_phiBool191		bool)
%----------------------------------------
(declare-variable	T_local__GET		(_ BitVec 1) )
(declare-variable	T_local__GET_i_filename		(_ BitVec 1) )
(declare-variable	T_local__GET_i_root		(_ BitVec 1) )
(declare-variable	T_local__POST		(_ BitVec 1) )
(declare-variable	T_local__POST_i_filename		(_ BitVec 1) )
(declare-variable	T_local__POST_i_root		(_ BitVec 1) )
(declare-variable	T_local__POST_i_text2edit		(_ BitVec 1) )
(declare-variable	T_v_a61de50		(_ BitVec 1) )
(declare-variable	T_v_a620858		(_ BitVec 1) )
(declare-variable	T_v_a620e54		(_ BitVec 1) )
(declare-variable	T_v_a620ef4		(_ BitVec 1) )
(declare-variable	T_v_a620f94		(_ BitVec 1) )
(declare-variable	T_v_a621034		(_ BitVec 1) )
(declare-variable	T_v_a621130		(_ BitVec 1) )
(declare-variable	T_v_a62f460		(_ BitVec 1) )
(declare-variable	T_v_a62f4d8		(_ BitVec 1) )
(declare-variable	T_v_a62f574		(_ BitVec 1) )
(declare-variable	T_v_a62f574_i_0bin00000000000000000000000000000001		(_ BitVec 1) )
(declare-variable	T_v_a62f9b8		(_ BitVec 1) )
(declare-variable	T_v_a633410		(_ BitVec 1) )
(declare-variable	T_v_a633488		(_ BitVec 1) )
(declare-variable	T_v_a6336e0		(_ BitVec 1) )
(declare-variable	T_v_a633b08		(_ BitVec 1) )
%----------------------------------------
(declare-variable	local__GET		Int)
(declare-variable	local__POST		Int)
(declare-variable	v_a6219d4		Int)
%========================================

% ASSERT( v_a62157c <=> v_a62139c OR v_a6214dc );
(assert (=  v_a62157c   (or v_a62139c v_a6214dc)   ) )
% ASSERT( T_v_a62f574_i_0bin00000000000000000000000000000001 = T_v_a62f574 );
(assert (=  T_v_a62f574_i_0bin00000000000000000000000000000001  T_v_a62f574  ) )
% ASSERT( T_v_a62f574 = T_v_a62f4d8);
(assert (=  T_v_a62f574  T_v_a62f4d8  ) )
% ASSERT( T_v_a62f4d8 = T_v_a62f460);
(assert (=  T_v_a62f4d8  T_v_a62f460  ) )
% ASSERT( v_phiBool180 <=>  v_a62f220  AND  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool180   (and v_a62f220 (not v_a6165e4))   ) )
% ASSERT( T_v_a62f460 = IF v_phiBool180 THEN T_local__GET_i_filename ELSE T_v_a62f460 ENDIF);
(assert (=  T_v_a62f460  (ite v_phiBool180 T_local__GET_i_filename T_v_a62f460)  ) )
% ASSERT( v_phiBool181 <=>  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool181  (not v_a6165e4)  ) )
% ASSERT( T_v_a62f460 = IF v_phiBool181 THEN T_v_a633b08 ELSE T_v_a62f460 ENDIF);
(assert (=  T_v_a62f460  (ite v_phiBool181 T_v_a633b08 T_v_a62f460)  ) )
% ASSERT( v_a62f220 <=> NOT v_a633c60 );
(assert (=  v_a62f220  (not v_a633c60)  ) )
% ASSERT( v_a633c60 <=> IF v_convertBool88 THEN TRUE ELSE FALSE ENDIF); % empty()
(assert (=  v_a633c60  (ite v_convertBool88 true false)  ) )
% ASSERT( T_local__GET_i_filename = T_local__GET );
(assert (=  T_local__GET_i_filename  T_local__GET  ) )
% ASSERT( T_local__GET = 0bin00000000000000000000000000000001 );
(assert (=  T_local__GET  #b1  ) )
% ASSERT( v_phiBool182 <=>  v_a6338c8  AND  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool182   (and v_a6338c8 (not v_a6165e4))   ) )
% ASSERT( T_v_a633b08 = IF v_phiBool182 THEN T_local__POST_i_filename ELSE T_v_a633b08 ENDIF);
(assert (=  T_v_a633b08  (ite v_phiBool182 T_local__POST_i_filename T_v_a633b08)  ) )
% ASSERT( v_a6338c8 <=> NOT v_a633838 );
(assert (=  v_a6338c8  (not v_a633838)  ) )
% ASSERT( v_a633838 <=> IF v_convertBool89 THEN TRUE ELSE FALSE ENDIF); % empty()
(assert (=  v_a633838  (ite v_convertBool89 true false)  ) )
% ASSERT( T_local__POST_i_filename = T_local__POST );
(assert (=  T_local__POST_i_filename  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_filename = T_local__POST );
(assert (=  T_local__POST_i_filename  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__GET_i_filename = T_local__GET );
(assert (=  T_local__GET_i_filename  T_local__GET  ) )
% ASSERT( T_local__GET = 0bin00000000000000000000000000000001 );
(assert (=  T_local__GET  #b1  ) )
% ASSERT( T_v_a62f574_i_0bin00000000000000000000000000000001 = T_v_a62f574 );
(assert (=  T_v_a62f574_i_0bin00000000000000000000000000000001  T_v_a62f574  ) )
% ASSERT( T_v_a6336e0 = 0bin00000000000000000000000000000001 );
(assert (=  T_v_a6336e0  #b1  ) )
% ASSERT( v_phiBool183 <=>  v_a6331f8  AND  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool183   (and v_a6331f8 (not v_a6165e4))   ) )
% ASSERT( T_v_a6336e0 = IF v_phiBool183 THEN T_v_a633410 ELSE T_v_a6336e0 ENDIF);
(assert (=  T_v_a6336e0  (ite v_phiBool183 T_v_a633410 T_v_a6336e0)  ) )
% ASSERT( v_a6331f8 <=> NOT v_a633168 );
(assert (=  v_a6331f8  (not v_a633168)  ) )
% ASSERT( v_a633168 <=> IF v_convertBool90 THEN TRUE ELSE FALSE ENDIF);
(assert (=  v_a633168  (ite v_convertBool90 true false)  ) )
% ASSERT( T_local__POST_i_text2edit = T_local__POST );
(assert (=  T_local__POST_i_text2edit  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_v_a633410 = T_local__POST_i_text2edit);
(assert (=  T_v_a633410  T_local__POST_i_text2edit  ) )
% ASSERT( T_local__POST_i_text2edit = T_local__POST );
(assert (=  T_local__POST_i_text2edit  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( v_phiBool184 <=>  v_a63350c  AND  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool184   (and v_a63350c (not v_a6165e4))   ) )
% ASSERT( T_v_a621130 = IF v_phiBool184 THEN T_v_a621034 ELSE T_v_a621130 ENDIF);
(assert (=  T_v_a621130  (ite v_phiBool184 T_v_a621034 T_v_a621130)  ) )
% ASSERT( v_phiBool185 <=>  ( NOT v_a63350c )  AND  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool185   (and (not v_a63350c) (not v_a6165e4))   ) )
% ASSERT( T_v_a621130 = IF v_phiBool185 THEN T_v_a62f4d8 ELSE T_v_a621130 ENDIF);
(assert (=  T_v_a621130  (ite v_phiBool185 T_v_a62f4d8 T_v_a621130)  ) )
% ASSERT( v_phiBool186 <=>  v_a6208dc  AND  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool186   (and v_a6208dc (not v_a6165e4))   ) )
% ASSERT( T_v_a633488 = IF v_phiBool186 THEN 0bin00000000000000000000000000000000 ELSE T_v_a633488 ENDIF);
(assert (=  T_v_a633488  (ite v_phiBool186 #b0 T_v_a633488)  ) )
% ASSERT( v_phiBool187 <=>  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool187  (not v_a6165e4)  ) )
% ASSERT( T_v_a633488 = IF v_phiBool187 THEN T_v_a620858 ELSE T_v_a633488 ENDIF);
(assert (=  T_v_a633488  (ite v_phiBool187 T_v_a620858 T_v_a633488)  ) )
% ASSERT( v_phiBool188 <=>  v_a62fba0  AND  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool188   (and v_a62fba0 (not v_a6165e4))   ) )
% ASSERT( T_v_a620858 = IF v_phiBool188 THEN T_local__GET_i_root ELSE T_v_a620858 ENDIF);
(assert (=  T_v_a620858  (ite v_phiBool188 T_local__GET_i_root T_v_a620858)  ) )
% ASSERT( v_phiBool189 <=>  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool189  (not v_a6165e4)  ) )
% ASSERT( T_v_a620858 = IF v_phiBool189 THEN T_v_a62f9b8 ELSE T_v_a620858 ENDIF);
(assert (=  T_v_a620858  (ite v_phiBool189 T_v_a62f9b8 T_v_a620858)  ) )
% ASSERT( v_a62fba0 <=> NOT v_a62fb10 );
(assert (=  v_a62fba0  (not v_a62fb10)  ) )
% ASSERT( v_a62fb10 <=> IF v_convertBool91 THEN TRUE ELSE FALSE ENDIF); % empty()
(assert (=  v_a62fb10  (ite v_convertBool91 true false)  ) )
% ASSERT( T_local__GET_i_root = T_local__GET );
(assert (=  T_local__GET_i_root  T_local__GET  ) )
% ASSERT( T_local__GET = 0bin00000000000000000000000000000001 );
(assert (=  T_local__GET  #b1  ) )
% ASSERT( v_phiBool190 <=>  v_a62f778  AND  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool190   (and v_a62f778 (not v_a6165e4))   ) )
% ASSERT( T_v_a62f9b8 = IF v_phiBool190 THEN T_local__POST_i_root ELSE T_v_a62f9b8 ENDIF);
(assert (=  T_v_a62f9b8  (ite v_phiBool190 T_local__POST_i_root T_v_a62f9b8)  ) )
% ASSERT( v_phiBool191 <=>  ( NOT v_a6165e4 )  );
(assert (=  v_phiBool191  (not v_a6165e4)  ) )
% ASSERT( T_v_a62f9b8 = IF v_phiBool191 THEN 0bin00000000000000000000000000000000 ELSE T_v_a62f9b8 ENDIF);
(assert (=  T_v_a62f9b8  (ite v_phiBool191 #b0 T_v_a62f9b8)  ) )
% ASSERT( v_a62f778 <=> NOT v_a62f6e8 );
(assert (=  v_a62f778  (not v_a62f6e8)  ) )
% ASSERT( v_a62f6e8 <=> IF v_convertBool92 THEN TRUE ELSE FALSE ENDIF); % empty()
(assert (=  v_a62f6e8  (ite v_convertBool92 true false)  ) )
% ASSERT( T_local__POST_i_root = T_local__POST );
(assert (=  T_local__POST_i_root  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__POST_i_root = T_local__POST );
(assert (=  T_local__POST_i_root  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( T_local__GET_i_root = T_local__GET );
(assert (=  T_local__GET_i_root  T_local__GET  ) )
% ASSERT( T_local__GET = 0bin00000000000000000000000000000001 );
(assert (=  T_local__GET  #b1  ) )
% ASSERT( T_v_a621034 = T_v_a620f94 | T_v_a62f4d8);
(assert (=  T_v_a621034   (bvor T_v_a620f94 T_v_a62f4d8)   ) )
% ASSERT( T_v_a620f94 = T_v_a620ef4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_a620f94   (bvor T_v_a620ef4 #b0)   ) )
% ASSERT( T_v_a620ef4 = T_v_a620e54 | T_v_a61de50);
(assert (=  T_v_a620ef4   (bvor T_v_a620e54 T_v_a61de50)   ) )
% ASSERT( T_v_a620e54 = T_v_a61de50 | 0bin00000000000000000000000000000000);
(assert (=  T_v_a620e54   (bvor T_v_a61de50 #b0)   ) )
% ASSERT( NOT v_a6165e4 );
(assert (not v_a6165e4) )
% ASSERT( v_a6211b4 );
(assert v_a6211b4 )
% ASSERT( v_a62157c );
(assert v_a62157c )

%========================================
(declare-variable	v_a631a44		String)
(declare-variable	v_a61de50		String)
(declare-variable	v_a62f574_i_0bin00000000000000000000000000000001		String)
(declare-variable	v_a62f4d8		String)
(declare-variable	v_a62f460		String)
(declare-variable	local__GET_i_filename		String)
(declare-variable	local__POST_i_filename		String)
(declare-variable	local__POST_i_text2edit		String)
(declare-variable	v_a633410		String)
(declare-variable	v_a6216c4		String)
(declare-variable	v_a621130		String)
(declare-variable	v_a633488		String)
(declare-variable	v_a620858		String)
(declare-variable	local__GET_i_root		String)
(declare-variable	local__POST_i_root		String)
(declare-variable	v_a621034		String)
(declare-variable	v_a620f94		String)
(declare-variable	v_a620ef4		String)
(declare-variable	v_a620e54		String)
(declare-variable   v_a62f574       String)
(declare-variable   v_a633b08       String)
(declare-variable   v_a6336e0       String)
(declare-variable   v_a62f9b8       String)
% ----------------------------------------------------------
% v_a6165e4 := v_a631a44 == ""
(assert (= v_a6165e4 (= v_a631a44 "") ) )
% v_a6211b4 := v_a61de50 == "write_changes"
(assert (= v_a6211b4 (= v_a61de50 "write_changes") ) )
% v_a62139c := v_a62f574_i_0bin00000000000000000000000000000001 == "txt"
(assert (= v_a62139c (= v_a62f574_i_0bin00000000000000000000000000000001 "txt") ) )
% v_a62f574 := v_a62f4d8
(assert (= v_a62f574 v_a62f4d8) )
% v_a62f4d8 := v_a62f460
(assert (= v_a62f4d8 v_a62f460) )
% v_phiBool180 | v_phiBool181 ? v_a62f460 := local__GET_i_filename | v_a633b08
(assert (=> v_phiBool180 (= v_a62f460 local__GET_i_filename) ) )
(assert (=> v_phiBool181 (= v_a62f460 v_a633b08) ) )
% v_convertBool88 := local__GET_i_filename != ""
(assert (= v_convertBool88 (not (= local__GET_i_filename "") ) ) )
% local__GET_i_filename := zYh_aNyStR
% v_phiBool182 ? v_a633b08 := local__POST_i_filename
(assert (=> v_phiBool182 (= v_a633b08 local__POST_i_filename) ) )
% v_convertBool89 := local__POST_i_filename != ""
(assert (= v_convertBool89 (not (= local__POST_i_filename "") ) ) )
% local__POST_i_filename := zYh_aNyStR
% v_a6214dc := v_a62f574_i_0bin00000000000000000000000000000001 == "fws"
(assert (= v_a6214dc (= v_a62f574_i_0bin00000000000000000000000000000001 "fws") ) )
% v_phiBool183 ? v_a6336e0 := v_a633410
(assert (=> v_phiBool183 (= v_a6336e0 v_a633410) ) )
% v_convertBool90 := local__POST_i_text2edit != ""
(assert (= v_convertBool90 (not (= local__POST_i_text2edit "") ) ) )
% local__POST_i_text2edit := zYh_aNyStR
% v_a633410 := local__POST_i_text2edit
(assert (= v_a633410 local__POST_i_text2edit) )
% v_a6216c4 := v_a621130
(assert (= v_a6216c4 v_a621130) )
% v_phiBool184 | v_phiBool185 ? v_a621130 := v_a621034 | v_a62f4d8
(assert (=> v_phiBool184 (= v_a621130 v_a621034) ) )
(assert (=> v_phiBool185 (= v_a621130 v_a62f4d8) ) )
% v_a63350c := v_a633488 == ""
(assert (= v_a63350c (= v_a633488 "") ) )
% v_phiBool186 | v_phiBool187 ? v_a633488 := "" | v_a620858
(assert (=> v_phiBool186 (= v_a633488 "") ) )
(assert (=> v_phiBool187 (= v_a633488 v_a620858) ) )
% v_a6208dc := v_a620858 == ""
(assert (= v_a6208dc (= v_a620858 "") ) )
% v_phiBool188 | v_phiBool189 ? v_a620858 := local__GET_i_root | v_a62f9b8
(assert (=> v_phiBool188 (= v_a620858 local__GET_i_root) ) )
(assert (=> v_phiBool189 (= v_a620858 v_a62f9b8) ) )
% v_convertBool91 := local__GET_i_root != ""
(assert (= v_convertBool91 (not (= local__GET_i_root "") ) ) )
% local__GET_i_root := zYh_aNyStR
% v_phiBool190 | v_phiBool191 ? v_a62f9b8 := local__POST_i_root | ""
(assert (=> v_phiBool190 (= v_a62f9b8 local__POST_i_root) ) )
(assert (=> v_phiBool191 (= v_a62f9b8 "") ) )
% v_convertBool92 := local__POST_i_root != ""
(assert (= v_convertBool92 (not (= local__POST_i_root "") ) ) )
% local__POST_i_root := zYh_aNyStR
% v_a621034 := v_a620f94 v_a62f4d8
(assert (= v_a621034 (Concat v_a620f94 v_a62f4d8) ) )
% v_a620f94 := v_a620ef4 "/"
(assert (= v_a620f94 (Concat v_a620ef4 "/") ) )
% v_a620ef4 := v_a620e54 v_a61de50
(assert (= v_a620ef4 (Concat v_a620e54 v_a61de50) ) )
% v_a620e54 := v_a61de50 "/"
(assert (= v_a620e54 (Concat v_a61de50 "/") ) )
% v_a61de50 := zYh_aNyStR
% v_a62f574_i_0bin00000000000000000000000000000001 := zYh_aNyStR
% v_a631a44 := zYh_aNyStR
% //===================================================================
% ==========================================================

(check-sat)
(get-model)

