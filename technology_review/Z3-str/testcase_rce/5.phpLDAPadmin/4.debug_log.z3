(declare-variable	v_a6adecc		bool)
(declare-variable	v_a6adf60		bool)
(declare-variable	v_a6ae16c		bool)
(declare-variable	v_a6ae37c		bool)
(declare-variable	v_a6ae41c		bool)
(declare-variable	v_a6ae4b0		bool)
(declare-variable	v_a6ae54c		bool)
(declare-variable	v_a6ae844		bool)
(declare-variable	v_a6ae8d8		bool)
(declare-variable	v_a6ae974		bool)
(declare-variable	v_a6aea08		bool)
(declare-variable	v_a6aeaa4		bool)
(declare-variable	v_a6aed9c		bool)
(declare-variable	v_a6aee30		bool)
(declare-variable	v_a6aeecc		bool)
(declare-variable	v_a6af25c		bool)
(declare-variable	v_a6af2fc		bool)
(declare-variable	v_a601250		bool)
(declare-variable	v_a6af774		bool)
(declare-variable	v_a6af958		bool)
(declare-variable	v_a6af9f0		bool)
(declare-variable	v_a6b117c		bool)
(declare-variable	v_a6b19cc		bool)
(declare-variable	v_a6b1a6c		bool)
(declare-variable	v_fileNameBool0		bool)
(declare-variable	v_phiBool1361		bool)
(declare-variable	v_phiBool1362		bool)
(declare-variable	v_phiBool1363		bool)
(declare-variable	v_phiBool1364		bool)
(declare-variable	v_phiBool1365		bool)
(declare-variable	v_phiBool1366		bool)
%----------------------------------------
(declare-variable	T_arg_a6ac8c8		(_ BitVec 1) )
(declare-variable	T_local__SERVER		(_ BitVec 1) )
(declare-variable	T_local__SERVER_i_HTTP_X_FORWARDED_FOR		(_ BitVec 1) )
(declare-variable	T_local__SERVER_i_REMOTE_ADDR		(_ BitVec 1) )
(declare-variable	T_v_a6ae16c		(_ BitVec 1) )
(declare-variable	T_v_a6ae37c		(_ BitVec 1) )
(declare-variable	T_v_a6ae844		(_ BitVec 1) )
(declare-variable	T_v_a6ae974		(_ BitVec 1) )
(declare-variable	T_v_a6aed9c		(_ BitVec 1) )
(declare-variable	T_v_a6af1bc		(_ BitVec 1) )
(declare-variable	T_v_a6af6d4		(_ BitVec 1) )
(declare-variable	T_v_a6af958		(_ BitVec 1) )
(declare-variable	T_v_a6b092c		(_ BitVec 1) )
(declare-variable	T_v_a6b117c		(_ BitVec 1) )
(declare-variable	T_v_a6b12c4		(_ BitVec 1) )
(declare-variable	T_v_a6b1370		(_ BitVec 1) )
(declare-variable	T_v_a6b1440		(_ BitVec 1) )
(declare-variable	T_v_a6b14dc		(_ BitVec 1) )
(declare-variable	T_v_a6b1598		(_ BitVec 1) )
(declare-variable	T_v_a6b19cc		(_ BitVec 1) )
(declare-variable	T_v_a6b1c44		(_ BitVec 1) )
%----------------------------------------
(declare-variable	local__SERVER		Int)
(declare-variable	local__SERVER_i_HTTP_X_FORWARDED_FOR		Int)
(declare-variable	v_a6af1bc		Int)
(declare-variable	local__SERVER_i_REMOTE_ADDR		Int)
(declare-variable	v_a6af6d4		Int)
(declare-variable	v_a6b092c		Int)
(declare-variable	v_a6b1440		Int)
(declare-variable	v_a6b1ce4		Int)
%========================================

% ASSERT( v_a6ae54c <=> v_a6adf60 OR v_a6ae4b0 );
(assert (=  v_a6ae54c   (or v_a6adf60 v_a6ae4b0)   ) )
% ASSERT( v_a6adf60 <=> NOT v_a6adecc );
(assert (=  v_a6adf60  (not v_a6adecc)  ) )
% ASSERT( v_a6ae4b0 <=> NOT v_a6ae41c );
(assert (=  v_a6ae4b0  (not v_a6ae41c)  ) )
% ASSERT( v_a6ae41c <=> v_a6ae16c OR v_a6ae37c );
(assert (=  v_a6ae41c   (or v_a6ae16c v_a6ae37c)   ) )
% ASSERT( T_v_a6ae16c = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: getValue()
(assert (=  T_v_a6ae16c  #b0 ) )
% ASSERT( T_v_a6ae37c = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: getValue()
(assert (=  T_v_a6ae37c  #b0 ) )
% ASSERT( v_a6aeaa4 <=> v_a6ae8d8 OR v_a6aea08 );
(assert (=  v_a6aeaa4   (or v_a6ae8d8 v_a6aea08)   ) )
% ASSERT( v_a6ae8d8 <=> NOT v_a6ae844 );
(assert (=  v_a6ae8d8  (not v_a6ae844)  ) )
% ASSERT( T_v_a6ae844 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: getValue()
(assert (=  T_v_a6ae844  #b0  ) )
% ASSERT( v_a6aea08 <=> NOT v_a6ae974 );
(assert (=  v_a6aea08  (not v_a6ae974)  ) )
% ASSERT( T_v_a6ae974 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: bitwise_and_fun()
(assert (=  T_v_a6ae974  #b0  ) )
% ASSERT( v_a6af9f0 <=> NOT v_a6af958 );
(assert (=  v_a6af9f0  (not v_a6af958)  ) )
% ASSERT( v_phiBool1361 <=>  v_a6af2fc  AND  v_a6aee30  AND  ( NOT v_a6aeaa4 )  AND  ( NOT v_a6ae54c )  );
(assert (=  v_phiBool1361  (and v_a6af2fc  (and v_a6aee30  (and  (not v_a6aeaa4 )  (not v_a6ae54c ) )  ) ) ) )
% ASSERT( v_a6af958 <=> IF v_phiBool1361 THEN TRUE ELSE v_a6af958 ENDIF );
(assert (=  v_a6af958  (ite v_phiBool1361 true v_a6af958)  ) )
% ASSERT( v_phiBool1362 <=>  v_a6af774  AND  ( NOT v_a6af2fc )  AND  v_a6aee30  AND  ( NOT v_a6aeaa4 )  AND  ( NOT v_a6ae54c )  );
(assert (=  v_phiBool1362  (and v_a6af774  (and  (not v_a6af2fc )  (and  v_a6aee30 (and  (not v_a6aeaa4 )  (not v_a6ae54c ) ) ) ) ) ) )
% ASSERT( v_a6af958 <=> IF v_phiBool1362 THEN TRUE ELSE v_a6af958 ENDIF );
(assert (=  v_a6af958  (ite v_phiBool1362 true v_a6af958)  ) )
% ASSERT( T_v_a6af958 = IF v_phiBool1362 THEN 0bin00000000000000000000000000000000 ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_a6af958  (ite v_phiBool1362 #b0 #b0)  ) )
% ASSERT( v_phiBool1363 <=>  ( NOT v_a6af774 )  AND  ( NOT v_a6af2fc )  AND  v_a6aee30  AND  ( NOT v_a6aeaa4 )  AND  ( NOT v_a6ae54c )  );
(assert (=  v_phiBool1363  (and (not v_a6af774 ) (and (not v_a6af2fc )  (and v_a6aee30  (and (not v_a6aeaa4 )  (not v_a6ae54c ) ) ) ) )  ) )
% ASSERT( v_a6af958 <=> IF v_phiBool1363 THEN FALSE ELSE v_a6af958 ENDIF );
(assert (=  v_a6af958  (ite v_phiBool1363 false v_a6af958)  ) )
% ASSERT( T_v_a6af958 = IF v_phiBool1363 THEN 0bin00000000000000000000000000000000 ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_a6af958  (ite v_phiBool1363 #b0 #b0)  ) )
% ASSERT( v_phiBool1364 <=>  ( NOT v_a6aee30 )  AND  ( NOT v_a6aeaa4 )  AND  ( NOT v_a6ae54c )  );
(assert (=  v_phiBool1364   (and (not v_a6aee30) (and (not v_a6aeaa4)  (not v_a6ae54c) ) )   ) )
% ASSERT( v_a6af958 <=> IF v_phiBool1364 THEN TRUE ELSE v_a6af958 ENDIF );
(assert (=  v_a6af958  (ite v_phiBool1364 true v_a6af958)  ) )
% ASSERT( T_v_a6af958 = IF v_phiBool1364 THEN 0bin00000000000000000000000000000000 ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_a6af958  (ite v_phiBool1364 #b0 #b0)  ) )
% ASSERT( v_a6aee30 <=> v_a6aed9c );
(assert (=  v_a6aee30  v_a6aed9c  ) )
% ASSERT( T_v_a6aed9c = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: getValue()
(assert (=  T_v_a6aed9c  #b0  ) )
% ASSERT( v_a6af2fc <=> v_a6aeecc AND v_a6af25c );
(assert (=  v_a6af2fc   (and v_a6aeecc v_a6af25c)   ) )
% ASSERT( v_a6af25c <=> (local__SERVER_i_HTTP_X_FORWARDED_FOR = v_a6af1bc) );
(assert (=  v_a6af25c  (= local__SERVER_i_HTTP_X_FORWARDED_FOR v_a6af1bc)  ) )
% ASSERT( T_local__SERVER_i_HTTP_X_FORWARDED_FOR = T_local__SERVER );
(assert (=  T_local__SERVER_i_HTTP_X_FORWARDED_FOR  T_local__SERVER  ) )
% ASSERT( T_v_a6af1bc = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: getValue()
(assert (=  T_v_a6af1bc  #b0 ) )
% ASSERT( v_a6af774 <=> (local__SERVER_i_REMOTE_ADDR = v_a6af6d4) );
(assert (=  v_a6af774  (= local__SERVER_i_REMOTE_ADDR v_a6af6d4 )  ) )
% ASSERT( T_local__SERVER_i_REMOTE_ADDR = T_local__SERVER );
(assert (=  T_local__SERVER_i_REMOTE_ADDR  T_local__SERVER  ) )
% ASSERT( T_v_a6af6d4 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: getValue()
(assert (=  T_v_a6af6d4  #b0  ) )
% ASSERT( v_a6b1a6c <=> v_a601250 OR v_a6b19cc );
(assert (=  v_a6b1a6c   (or v_a601250 v_a6b19cc)   ) )
% ASSERT( T_v_a6b19cc = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: getValue()
(assert (=  T_v_a6b19cc  #b0  ) )
% ASSERT( T_v_a6b1c44 = 0bin00000000000000000000000000000001 );
(assert (=  T_v_a6b1c44  #b1  ) )
% ASSERT( v_fileNameBool0 );
(assert v_fileNameBool0 )
% ASSERT( T_v_a6b1c44 = T_v_a6b1598 | 0bin00000000000000000000000000000000);
(assert (=  T_v_a6b1c44   (bvor T_v_a6b1598 #b0)   ) )
% ASSERT( v_phiBool1365 <=>  v_a6b117c  AND  ( NOT v_a6af9f0 )  AND  ( NOT v_a6aeaa4 )  AND  ( NOT v_a6ae54c )  );
(assert (=  v_phiBool1365  (and v_a6b117c  (and  (not v_a6af9f0 )  (and  (not v_a6aeaa4 ) (not v_a6ae54c ) ) ) ) ) )
% ASSERT( T_v_a6b1598 = IF v_phiBool1365 THEN T_v_a6b1370 ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_a6b1598  (ite v_phiBool1365 T_v_a6b1370 #b0)  ) )
% ASSERT( v_phiBool1366 <=>  ( NOT v_a6b117c )  AND  ( NOT v_a6af9f0 )  AND  ( NOT v_a6aeaa4 )  AND  ( NOT v_a6ae54c )  );
(assert (=  v_phiBool1366  (and (not v_a6b117c) (and (not v_a6af9f0) (and (not v_a6aeaa4 )  (not v_a6ae54c) ) ) ) ) )
% ASSERT( T_v_a6b117c = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: preg_match()
(assert (=  T_v_a6b117c  #b0 ) )
% ASSERT( T_v_a6b1370 = T_arg_a6ac8c8);
(assert (=  T_v_a6b1370  T_arg_a6ac8c8  ) )
% ASSERT( T_v_a6b12c4 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: join()
(assert (=  T_v_a6b12c4  #b0  ) )
% ASSERT( T_v_a6b092c = 0bin00000000000000000000000000000000);
(assert (=  T_v_a6b092c  #b0  ) )
% ASSERT( T_v_a6b1440 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: array_values()
(assert (=  T_v_a6b1440  #b0  ) )
% ASSERT( NOT v_a6ae54c );
(assert (not v_a6ae54c) )
% ASSERT( NOT v_a6aeaa4 );
(assert (not v_a6aeaa4) )
% ASSERT( NOT v_a6af9f0 );
(assert (not v_a6af9f0) )
% ASSERT( v_a6b1a6c );
(assert v_a6b1a6c )

%========================================
(declare-variable	v_a6b1ba8		String)
(declare-variable	v_fileName0		String)
(declare-variable	v_a6b1c44		String)
(declare-variable	v_a6b1598		String)
(declare-variable	v_a6b1370		String)
(declare-variable	arg_a6ac8c8		String)
(declare-variable   tmp     String)
(declare-variable   v_a6b14dc     String)
% ----------------------------------------------------------
% //***** String CSTR =================================================
% v_fileName0 := zYh_aNyStR ".php"
(assert (= v_fileName0 (Concat tmp ".php") ) )
% v_fileNameBool0 := v_a6b1ba8 == v_fileName0
(assert (= v_fileNameBool0 (= v_a6b1ba8 v_fileName0) ) )
% v_a6b1ba8 := "/tmp/pla_debug.log"
(assert (= v_a6b1ba8 "/tmp/pla_debug.log") )
% v_a6b1c44 := v_a6b1598 "\n"
(assert (= v_a6b1c44 (Concat v_a6b1598 "_^n^") ) )
% v_phiBool1365 | v_phiBool1366 ? v_a6b1598 := v_a6b1370 | v_a6b14dc
(assert (=> v_phiBool1365 (= v_a6b1598 v_a6b1370) ) )
(assert (=> v_phiBool1366 (= v_a6b1598 v_a6b14dc) ) )
% v_a6b1370 := arg_a6ac8c8
(assert (= v_a6b1370 arg_a6ac8c8) )
% arg_a6ac8c8 := zYh_aNyStR
% v_a6b14dc := zYh_aNyStR
% //===================================================================
% ==========================================================

(check-sat)
(get-model)

