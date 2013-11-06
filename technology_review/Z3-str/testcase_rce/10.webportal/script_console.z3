(declare-variable	v_8a919a4		bool)
%----------------------------------------
(declare-variable	T_local__GET		(_ BitVec 1) )
(declare-variable	T_local__GET_i_action		(_ BitVec 1) )
(declare-variable	T_local__POST		(_ BitVec 1) )
(declare-variable	T_local__POST_i_code		(_ BitVec 1) )
(declare-variable	T_v_8a91bc0		(_ BitVec 1) )
%----------------------------------------
(declare-variable	local__GET		Int)
(declare-variable	local__POST		Int)
(declare-variable	v_8a91c50		Int)
%========================================

% ASSERT( T_local__GET_i_action = T_local__GET );
(assert (=  T_local__GET_i_action  T_local__GET  ) )
% ASSERT( T_local__GET = 0bin00000000000000000000000000000001 );
(assert (=  T_local__GET  #b1  ) )
% ASSERT( T_v_8a91bc0 = 0bin00000000000000000000000000000001 );
(assert (=  T_v_8a91bc0  #b1  ) )
% ASSERT( T_v_8a91bc0 = T_local__POST_i_code);
(assert (=  T_v_8a91bc0  T_local__POST_i_code  ) )
% ASSERT( T_local__POST_i_code = T_local__POST );
(assert (=  T_local__POST_i_code  T_local__POST  ) )
% ASSERT( T_local__POST = 0bin00000000000000000000000000000001 );
(assert (=  T_local__POST  #b1  ) )
% ASSERT( v_8a919a4 );
(assert v_8a919a4 )

%========================================
(declare-variable	local__GET_i_action		String)
(declare-variable	v_8a91bc0		String)
(declare-variable	local__POST_i_code		String)
% ----------------------------------------------------------
% v_8a919a4 := local__GET_i_action == "execute"
(assert (= v_8a919a4 (= local__GET_i_action "execute") ) )
% local__GET_i_action := zYh_aNyStR
% v_8a91bc0 := local__POST_i_code
(assert (= v_8a91bc0 local__POST_i_code) )
% local__POST_i_code := zYh_aNyStR
% //===================================================================
% ==========================================================

(check-sat)
(get-model)

