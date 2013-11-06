(declare-variable	v_a530750		bool)
(declare-variable	v_22_a535c00		bool)
(declare-variable	v_22_a535c44		bool)
(declare-variable	v_a530414		bool)
(declare-variable	v_a5304a8		bool)
(declare-variable	v_a5307a0		bool)
%----------------------------------------
(declare-variable	T_v_a530750		(_ BitVec 1) )
(declare-variable	T_v_22_a535c00		(_ BitVec 1) )
(declare-variable	T_v_a5246fc		(_ BitVec 1) )
(declare-variable	T_v_a52479c		(_ BitVec 1) )
(declare-variable	T_v_a530414		(_ BitVec 1) )
(declare-variable	T_v_a530a94		(_ BitVec 1) )
%----------------------------------------
(declare-variable	v_a524830		Int)
%========================================

% ASSERT( v_a5304a8 <=> NOT v_a530414 );
(assert (=  v_a5304a8  (not v_a530414)  ) )
% ASSERT( T_v_a530414 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: get_cached_item()
(assert (=  T_v_a530414  #b0 ) )
% ASSERT( v_a5307a0 <=> NOT v_a530750 );
(assert (=  v_a5307a0  (not v_a530750)  ) )
% ASSERT( v_a530750 <=> v_22_a535c00 );
(assert (=  v_a530750  v_22_a535c00  ) )
% ASSERT( T_v_a530750 = T_v_22_a535c00 );
(assert (=  T_v_a530750  T_v_22_a535c00  ) )
% ASSERT( T_v_22_a535c00 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: getServer()
(assert (=  T_v_22_a535c00  #b0 ) )
% ASSERT( T_v_a52479c = 0bin00000000000000000000000000000001 );
(assert (=  T_v_a52479c  #b1  ) )
% ASSERT( T_v_a52479c = T_v_a5246fc | 0bin00000000000000000000000000000000);
(assert (=  T_v_a52479c   (bvor T_v_a5246fc #b0)   ) )
% ASSERT( T_v_a5246fc = 0bin00000000000000000000000000000000 | T_v_a530a94);
(assert (=  T_v_a5246fc   (bvor #b0 T_v_a530a94)   ) )
% ASSERT( T_v_a530a94 = 0bin00000000000000000000000000000000); % Do not taint for unsummarized function: getValue()
(assert (=  T_v_a530a94  #b0 ) )
% ASSERT( v_a5304a8 );
(assert v_a5304a8 )
% ASSERT( NOT v_a5307a0 );
(assert (not v_a5307a0) )

%========================================
(declare-variable	v_a52479c		String)
(declare-variable	v_a5246fc		String)
(declare-variable   v_a530a94       String)

% ----------------------------------------------------------
% //***** String CSTR =================================================
% v_a52479c := v_a5246fc "($server_id);"
(assert (= v_a52479c (Concat v_a5246fc "_^do^server_id_^sc^") ) )
% v_a5246fc := "$tree = new " v_a530a94
(assert (= v_a5246fc (Concat "_^do^tree_=_new" v_a530a94) ) )
% //[**] v_a530a94 := getValue("appearance", "tree")
% //===================================================================
% ==========================================================

(check-sat)
(get-model)

