(declare-variable	v_4_a5ca2a8_i_app_i_use_log		bool)
(declare-variable	v_4_a5f50e8		bool)
(declare-variable	v_4_a5f5260		bool)
(declare-variable	v_4_a5f58e8		bool)
(declare-variable	v_4_a5f5978		bool)
(declare-variable	v_4_a5f5afc		String)
(declare-variable	v_4_a5f5b90		bool)
(declare-variable	v_4_convertBool2		bool)
(declare-variable	v_4_fileNameBool0		bool)
(declare-variable	v_4_phiBool6		bool)
(declare-variable	v_4_phiBool7		bool)
(declare-variable	v_4_a5f66e0		bool)
(declare-variable	v_4_convertBool3		bool)
(declare-variable	v_4_fileNameBool1		bool)
(declare-variable	v_4_phiBool8		bool)
(declare-variable	v_4_phiBool9		bool)
(declare-variable	v_4_convertBool5		bool)
(declare-variable	v_4_fileNameBool3		bool)
(declare-variable	v_4_phiBool12		bool)
(declare-variable	v_4_phiBool13		bool)
(declare-variable	v_4_convertBool6		bool)
(declare-variable	v_4_fileNameBool4		bool)
(declare-variable	v_4_phiBool14		bool)
(declare-variable	v_4_phiBool15		bool)
(declare-variable	v_4_convertBool7		bool)
(declare-variable	v_4_fileNameBool5		bool)
(declare-variable	v_4_phiBool16		bool)
(declare-variable	v_4_phiBool17		bool)
%----------------------------------------
(declare-variable	T_v_a5f7d64		(_ BitVec 1) )
(declare-variable	T_local__SESSION_i_sessionID		(_ BitVec 1) )
(declare-variable	T_local__SERVER		(_ BitVec 1) )
(declare-variable	T_local__SERVER_i_REMOTE_ADDR		(_ BitVec 1) )
(declare-variable	T_v_4_a5ca2a8		(_ BitVec 1) )
(declare-variable	T_v_4_a5ca2a8_i_app		(_ BitVec 1) )
(declare-variable	T_v_4_a5ca2a8_i_app_i_use_log		(_ BitVec 1) )
(declare-variable	T_v_4_a5f54a0		(_ BitVec 1) )
(declare-variable	T_v_4_a5f58e8		(_ BitVec 1) )
(declare-variable	T_v_4_a5f5df8		(_ BitVec 1) )
(declare-variable	T_v_4_a5f5e94		(_ BitVec 1) )
(declare-variable	T_v_4_a5f5f34		(_ BitVec 1) )
(declare-variable	T_v_4_a5f5fd4		(_ BitVec 1) )
(declare-variable	T_v_4_a5f6074		(_ BitVec 1) )
(declare-variable	T_v_4_a5f6114		(_ BitVec 1) )
(declare-variable	T_v_4_a5f61b4		(_ BitVec 1) )
(declare-variable	T_v_4_a5f6254		(_ BitVec 1) )
(declare-variable	T_v_4_a5f62f4		(_ BitVec 1) )
(declare-variable	T_v_4_a5f6394		(_ BitVec 1) )
(declare-variable	T_v_4_a5f6858		(_ BitVec 1) )
(declare-variable	T_v_4_a5f68f4		(_ BitVec 1) )
(declare-variable	T_v_4_a5f6948		(_ BitVec 1) )
(declare-variable	T_v_a5f7ef0		(_ BitVec 1) )
(declare-variable   T_local__SESSION     (_ BitVec 1) )
(declare-variable	T_v_a5f7c18		(_ BitVec 1) )
(declare-variable	T_v_5_a5f8e8c		(_ BitVec 1) )
(declare-variable	T_v_a5f7b84		(_ BitVec 1) )
(declare-variable	T_v_a5f7c18_i_scheduletitle		(_ BitVec 1) )
%----------------------------------------
(declare-variable	local__SERVER		Int)
(declare-variable	v_4_a5ca2a8_i_app		Int)
(declare-variable	v_4_a5f664c		Int)
(declare-variable	v_4_a5f68f4		Int)
(declare-variable	v_4_a5f6948		Int)
(declare-variable	v_a5f7ef0		Int)
(declare-variable	v_4_a5f69cc		Int)
(declare-variable	v_a5f7c18		Int)
(declare-variable	v_5_a5f8e8c		Int)
(declare-variable	v_5_a5fb284		Int)
%========================================

% ASSERT( v_4_a5f50e8 <=> NOT v_4_a5ca2a8_i_app_i_use_log );
(assert (=  v_4_a5f50e8  (not v_4_a5ca2a8_i_app_i_use_log)  ) )
% ASSERT( T_v_4_a5ca2a8_i_app_i_use_log = T_v_4_a5ca2a8_i_app );
(assert (=  T_v_4_a5ca2a8_i_app_i_use_log  T_v_4_a5ca2a8_i_app  ) )
% ASSERT( T_v_4_a5ca2a8_i_app = T_v_4_a5ca2a8 );
(assert (=  T_v_4_a5ca2a8_i_app  T_v_4_a5ca2a8  ) )
% ASSERT( v_4_a5f5978 <=> NOT v_4_a5f58e8 );
(assert (=  v_4_a5f5978  (not v_4_a5f58e8)  ) )
% ASSERT( T_v_4_a5f58e8 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: touch()
(assert (=  T_v_4_a5f58e8  #b0  ) )
% ASSERT( v_4_a5f5b90 <=> NOT v_4_a5f5afc );
(assert (=  v_4_a5f5b90  (not (= v_4_a5f5afc "") )  ) )
% ASSERT( T_v_4_a5f6394 = 0bin00000000000000000000000000000001 );
(assert (=  T_v_4_a5f6394  #b1  ) )
% ASSERT( v_4_fileNameBool0 );
(assert v_4_fileNameBool0 )
% ASSERT( T_v_4_a5f6394 = T_v_4_a5f62f4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_4_a5f6394   (bvor T_v_4_a5f62f4 #b0)   ) )
% ASSERT( T_v_4_a5f62f4 = T_v_4_a5f6254 | T_v_4_a5f54a0);
(assert (=  T_v_4_a5f62f4   (bvor T_v_4_a5f6254 T_v_4_a5f54a0)   ) )
% ASSERT( v_4_phiBool6 <=>  v_4_a5f5260  AND  ( NOT v_4_a5f50e8 )  );
(assert (=  v_4_phiBool6   (and v_4_a5f5260 (not v_4_a5f50e8))   ) )
% ASSERT( T_v_4_a5f54a0 = IF v_4_phiBool6 THEN T_local__SERVER_i_REMOTE_ADDR ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_4_a5f54a0  (ite v_4_phiBool6 T_local__SERVER_i_REMOTE_ADDR #b0)  ) )
% ASSERT( v_4_phiBool7 <=>  ( NOT v_4_a5f50e8 )  );
(assert (=  v_4_phiBool7  (not v_4_a5f50e8)  ) )
% ASSERT( T_v_4_a5f54a0 = IF v_4_phiBool7 THEN 0bin00000000000000000000000000000000 ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_4_a5f54a0  (ite v_4_phiBool7 #b0 #b0)  ) )
% ASSERT( v_4_a5f5260 <=> IF v_4_convertBool2 THEN TRUE ELSE FALSE ENDIF); % empty()
(assert (=  v_4_a5f5260  (ite v_4_convertBool2 true false)  ) )
% ASSERT( T_local__SERVER_i_REMOTE_ADDR = T_local__SERVER );
(assert (=  T_local__SERVER_i_REMOTE_ADDR  T_local__SERVER  ) )
% ASSERT( T_v_4_a5f6254 = T_v_4_a5f61b4 | 0bin00000000000000000000000000000000);
(assert (=  T_v_4_a5f6254   (bvor T_v_4_a5f61b4 #b0)   ) )
% ASSERT( T_v_4_a5f61b4 = T_v_4_a5f6114 | T_local__SESSION_i_sessionID);
(assert (=  T_v_4_a5f61b4   (bvor T_v_4_a5f6114 T_local__SESSION_i_sessionID)   ) )
% ASSERT( T_v_4_a5f6114 = T_v_4_a5f6074 | 0bin00000000000000000000000000000000);
(assert (=  T_v_4_a5f6114   (bvor T_v_4_a5f6074 #b0)   ) )
% ASSERT( T_v_4_a5f6074 = T_v_4_a5f5fd4 | T_v_a5f7d64);
(assert (=  T_v_4_a5f6074   (bvor T_v_4_a5f5fd4 T_v_a5f7d64)   ) )
% ASSERT( T_v_4_a5f5fd4 = T_v_4_a5f5f34 | 0bin00000000000000000000000000000000);
(assert (=  T_v_4_a5f5fd4   (bvor T_v_4_a5f5f34 #b0)   ) )
% ASSERT( T_v_4_a5f5f34 = T_v_4_a5f5e94 | 0bin00000000000000000000000000000000);
(assert (=  T_v_4_a5f5f34   (bvor T_v_4_a5f5e94 #b0)   ) )
% ASSERT( T_v_4_a5f5e94 = 0bin00000000000000000000000000000000 | T_v_4_a5f5df8);
(assert (=  T_v_4_a5f5e94   (bvor #b0 T_v_4_a5f5df8)   ) )
% ASSERT( T_v_4_a5f5df8 = 0bin00000000000000000000000000000000);
(assert (=  T_v_4_a5f5df8  #b0  ) )
% ASSERT( v_4_a5f66e0 <=> NOT ( v_4_a5f664c = 0bin00000000000000000000000000000000) );
(assert (=  v_4_a5f66e0  (not (= v_4_a5f664c 0))  ) )
% ASSERT( v_4_fileNameBool1 );
(assert v_4_fileNameBool1 )
% ASSERT( v_4_phiBool8 <=>  v_4_a5f5260  AND  ( NOT v_4_a5f50e8 )  );
(assert (=  v_4_phiBool8   (and v_4_a5f5260 (not v_4_a5f50e8))   ) )
% ASSERT( T_v_4_a5f54a0 = IF v_4_phiBool8 THEN T_local__SERVER_i_REMOTE_ADDR ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_4_a5f54a0  (ite v_4_phiBool8 T_local__SERVER_i_REMOTE_ADDR #b0)  ) )
% ASSERT( v_4_phiBool9 <=>  ( NOT v_4_a5f50e8 )  );
(assert (=  v_4_phiBool9  (not v_4_a5f50e8)  ) )
% ASSERT( T_v_4_a5f54a0 = IF v_4_phiBool9 THEN 0bin00000000000000000000000000000000 ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_4_a5f54a0  (ite v_4_phiBool9 #b0 #b0)  ) )
% ASSERT( v_4_a5f5260 <=> IF v_4_convertBool3 THEN TRUE ELSE FALSE ENDIF); % empty()
(assert (=  v_4_a5f5260  (ite v_4_convertBool3 true false)  ) )
% ASSERT( v_4_fileNameBool3 );
(assert v_4_fileNameBool3 )
% ASSERT( v_4_phiBool12 <=>  v_4_a5f5260  AND  ( NOT v_4_a5f50e8 )  );
(assert (=  v_4_phiBool12   (and v_4_a5f5260 (not v_4_a5f50e8))   ) )
% ASSERT( T_v_4_a5f54a0 = IF v_4_phiBool12 THEN T_local__SERVER_i_REMOTE_ADDR ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_4_a5f54a0  (ite v_4_phiBool12 T_local__SERVER_i_REMOTE_ADDR #b0)  ) )
% ASSERT( v_4_phiBool13 <=>  ( NOT v_4_a5f50e8 )  );
(assert (=  v_4_phiBool13  (not v_4_a5f50e8)  ) )
% ASSERT( T_v_4_a5f54a0 = IF v_4_phiBool13 THEN 0bin00000000000000000000000000000000 ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_4_a5f54a0  (ite v_4_phiBool13 #b0 #b0)  ) )
% ASSERT( v_4_a5f5260 <=> IF v_4_convertBool5 THEN TRUE ELSE FALSE ENDIF); % empty()
(assert (=  v_4_a5f5260  (ite v_4_convertBool5 true false)  ) )
% ASSERT( T_v_4_a5f6858 = 0bin00000000000000000000000000000000);
(assert (=  T_v_4_a5f6858  #b0  ) )
% ASSERT( v_4_fileNameBool4 );
(assert v_4_fileNameBool4 )
% ASSERT( v_4_phiBool14 <=>  v_4_a5f5260  AND  ( NOT v_4_a5f50e8 )  );
(assert (=  v_4_phiBool14   (and v_4_a5f5260 (not v_4_a5f50e8))   ) )
% ASSERT( T_v_4_a5f54a0 = IF v_4_phiBool14 THEN T_local__SERVER_i_REMOTE_ADDR ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_4_a5f54a0  (ite v_4_phiBool14 T_local__SERVER_i_REMOTE_ADDR #b0)  ) )
% ASSERT( v_4_phiBool15 <=>  ( NOT v_4_a5f50e8 )  );
(assert (=  v_4_phiBool15  (not v_4_a5f50e8)  ) )
% ASSERT( T_v_4_a5f54a0 = IF v_4_phiBool15 THEN 0bin00000000000000000000000000000000 ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_4_a5f54a0  (ite v_4_phiBool15 #b0 #b0)  ) )
% ASSERT( v_4_a5f5260 <=> IF v_4_convertBool6 THEN TRUE ELSE FALSE ENDIF); % empty()
(assert (=  v_4_a5f5260  (ite v_4_convertBool6 true false)  ) )
% ASSERT( T_v_4_a5f68f4 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: flock()
(assert (=  T_v_4_a5f68f4  #b0  ) )
% ASSERT( v_4_fileNameBool5 );
(assert v_4_fileNameBool5 )
% ASSERT( v_4_phiBool16 <=>  v_4_a5f5260  AND  ( NOT v_4_a5f50e8 )  );
(assert (=  v_4_phiBool16   (and v_4_a5f5260 (not v_4_a5f50e8))   ) )
% ASSERT( T_v_4_a5f54a0 = IF v_4_phiBool16 THEN T_local__SERVER_i_REMOTE_ADDR ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_4_a5f54a0  (ite v_4_phiBool16 T_local__SERVER_i_REMOTE_ADDR #b0)  ) )
% ASSERT( v_4_phiBool17 <=>  ( NOT v_4_a5f50e8 )  );
(assert (=  v_4_phiBool17  (not v_4_a5f50e8)  ) )
% ASSERT( T_v_4_a5f54a0 = IF v_4_phiBool17 THEN 0bin00000000000000000000000000000000 ELSE 0bin00000000000000000000000000000000 ENDIF);
(assert (=  T_v_4_a5f54a0  (ite v_4_phiBool17 #b0 #b0)  ) )
% ASSERT( v_4_a5f5260 <=> IF v_4_convertBool7 THEN TRUE ELSE FALSE ENDIF); % empty()
(assert (=  v_4_a5f5260  (ite v_4_convertBool7 true false)  ) )
% ASSERT( T_v_4_a5f6948 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: fclose1()
(assert (=  T_v_4_a5f6948  #b0  ) )
% ASSERT( v_a5f7ef0 = 0bin00000000000000000000000000000000 );
(assert (=  v_a5f7ef0 0  ) )
% ASSERT( T_v_a5f7ef0 = 0bin00000000000000000000000000000000 );
(assert (=  T_v_a5f7ef0  #b0  ) )
% ASSERT( T_v_a5f7d64 = 0bin00000000000000000000000000000000 | T_v_a5f7c18_i_scheduletitle);
(assert (=  T_v_a5f7d64   (bvor #b0 T_v_a5f7c18_i_scheduletitle)   ) )
% ASSERT( T_v_a5f7c18_i_scheduletitle = T_v_a5f7c18 );
(assert (=  T_v_a5f7c18_i_scheduletitle  T_v_a5f7c18  ) )
% ASSERT( v_a5f7c18 = v_5_a5f8e8c );
(assert (=  v_a5f7c18  v_5_a5f8e8c  ) )
% ASSERT( T_v_a5f7c18 = T_v_5_a5f8e8c );
(assert (=  T_v_a5f7c18  T_v_5_a5f8e8c  ) )
% ASSERT( T_v_5_a5f8e8c = 0bin00000000000000000000000000000000);
(assert (=  T_v_5_a5f8e8c  #b0  ) )
% ASSERT( T_v_a5f7b84 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: cleanPostVals()
(assert (=  T_v_a5f7b84  #b0  ) )
% ASSERT( T_local__SESSION_i_sessionID = T_local__SESSION );
(assert (=  T_local__SESSION_i_sessionID  T_local__SESSION  ) )

%========================================
(declare-variable	v_4_fileName0		String)
(declare-variable	v_4_a5f6394		String)
(declare-variable	v_4_a5f62f4		String)
(declare-variable	v_4_a5f6254		String)
(declare-variable	v_4_a5f54a0		String)
(declare-variable	v_4_a5f61b4		String)
(declare-variable	v_4_a5f6114		String)
(declare-variable	local__SESSION_i_sessionID		String)
(declare-variable	v_4_a5f6074		String)
(declare-variable	v_4_a5f5fd4		String)
(declare-variable	v_a5f7d64		String)
(declare-variable	v_4_a5f5f34		String)
(declare-variable	v_4_a5f5e94		String)
(declare-variable	v_4_a5f5df8		String)
(declare-variable	v_4_fileName1		String)
(declare-variable	v_4_fileName3		String)
(declare-variable	v_4_fileName4		String)
(declare-variable	v_4_fileName5		String)
(declare-variable   local__SERVER_i_REMOTE_ADDR       String)
(declare-variable   v_a5f7c18_i_scheduletitle       String)
% ----------------------------------------------------------
% //***** String CSTR =================================================
% v_4_a5f5afc := "/var/log/phpscheduleitlog.txt"
(assert (= v_4_a5f5afc "/var/log/phpscheduleitlog.txt") )
% v_4_fileName0 := zYh_aNyStR ".php"
% v_4_fileNameBool0 := v_4_a5f5afc == v_4_fileName0
(assert (= v_4_fileNameBool0 (= v_4_a5f5afc v_4_fileName0) ) )
% v_4_a5f6394 := v_4_a5f62f4 "\r\n"
(assert (= v_4_a5f6394 (Concat v_4_a5f62f4 "_^r_^n^") ) )
% v_4_a5f62f4 := v_4_a5f6254 v_4_a5f54a0
(assert (= v_4_a5f62f4 (Concat v_4_a5f6254 v_4_a5f54a0) ) )
% v_4_phiBool6 | v_4_phiBool7 ? v_4_a5f54a0 := local__SERVER_i_REMOTE_ADDR | ""
(assert (=> v_4_phiBool6 (= v_4_a5f54a0 local__SERVER_i_REMOTE_ADDR) ) )
(assert (=> v_4_phiBool7 (= v_4_a5f54a0 "") ) )
% v_4_convertBool2 := "" != ""
(assert (= v_4_convertBool2 (not (= "" "") ) ) )
% local__SERVER_i_REMOTE_ADDR := zYh_aNyStR
% v_4_a5f6254 := v_4_a5f61b4 "\t"
(assert (= v_4_a5f6254 (Concat v_4_a5f61b4 "_^t") ) )
% v_4_a5f61b4 := v_4_a5f6114 local__SESSION_i_sessionID
(assert (= v_4_a5f61b4 (Concat v_4_a5f6114 local__SESSION_i_sessionID) ) )
% v_4_a5f6114 := v_4_a5f6074 "\t"
(assert (= v_4_a5f6114 (Concat v_4_a5f6074 "_^t") ) )
% v_4_a5f6074 := v_4_a5f5fd4 v_a5f7d64
(assert (= v_4_a5f6074 (Concat v_4_a5f5fd4 v_a5f7d64) ) )
% v_4_a5f5fd4 := v_4_a5f5f34 "\t"
(assert (= v_4_a5f5fd4 (Concat v_4_a5f5f34 "_^t") ) )
% v_4_a5f5f34 := v_4_a5f5e94 "]"
(assert (= v_4_a5f5f34 (Concat v_4_a5f5e94 "_^rf^") ) )
% v_4_a5f5e94 := "[" v_4_a5f5df8
(assert (= v_4_a5f5e94 "_^lf_" v_4_a5f5df8) )
% v_4_a5f5df8 := "D, d M Y H:i:s"
(assert (= v_4_a5f5df8 "D_d_M_Y_H_i_s") )
% v_4_fileName1 := zYh_aNyStR ".php"
% v_4_fileNameBool1 := v_4_a5f5afc == v_4_fileName1
(assert (= v_4_fileNameBool1 (= v_4_a5f5afc v_4_fileName1) ) )
% v_4_convertBool3 := "" != ""
(assert (= v_4_convertBool3 (not (= "" "") ) ) )
% v_4_fileName3 := zYh_aNyStR ".php"
% v_4_fileNameBool3 := v_4_a5f5afc == v_4_fileName3
(assert (= v_4_fileNameBool3 (= v_4_a5f5afc v_4_fileName3) ) )
% v_4_convertBool5 := "" != ""
(assert (= v_4_convertBool5 (not (= "" "") ) ) )
% // v_4_a5f6858 := _zyh_getConstant( "LOCK_UN")
% v_4_a5f6858 := zYh_aNyStR
% v_4_fileName4 := zYh_aNyStR ".php"
% v_4_fileNameBool4 := v_4_a5f5afc == v_4_fileName4
(assert (= v_4_fileNameBool4 (= v_4_a5f5afc v_4_fileName4) ) )
% v_4_convertBool6 := "" != ""
(assert (= v_4_convertBool6 (not (= "" "") ) ) )
% v_4_fileName5 := zYh_aNyStR ".php"
% v_4_fileNameBool5 := v_4_a5f5afc == v_4_fileName5
(assert (= v_4_fileNameBool5 (= v_4_a5f5afc v_4_fileName5) ) )
% v_4_convertBool7 := "" != ""
(assert (= v_4_convertBool7 (not (= "" "") ) ) )
% v_a5f7d64 := "Schedule added. " v_a5f7c18_i_scheduletitle
(assert (= v_a5f7d64 (Concat "Schedule_added." v_a5f7c18_i_scheduletitle) ) )
% local__SESSION_i_sessionID := zYh_aNyStR
% v_a5f7c18_i_scheduletitle := zYh_aNyStR
% //[**] v_a5f7b84 := cleanPostVals()
% //===================================================================
% ==========================================================

(check-sat)
(get-model)

