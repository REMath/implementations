(declare-variable  T_2  bool)
(declare-variable  PCTEMP_LHS_1  bool)
%------------
(declare-variable  PCTEMP_LHS_1_len_0  Int)
%------------
(declare-variable  T2_2  String)
(declare-variable  T0_2  String)
(declare-variable  PCTEMP_LHS_1_group_1  String)
(declare-variable  PCTEMP_LHS_1_idx_0  String)
(declare-variable  T1_2  String)
(declare-variable  var_0xINPUT_9  String)

%============================================

(assert (=> PCTEMP_LHS_1 (= var_0xINPUT_9 (Concat T0_2 T1_2) ) ) )
(assert (=> PCTEMP_LHS_1 (= T1_2 (Concat PCTEMP_LHS_1_idx_0 T2_2) ) ) )
(assert (= T_2 (= PCTEMP_LHS_1 false) ) )
(assert T_2)
(assert (=> PCTEMP_LHS_1 (= PCTEMP_LHS_1_group_1 PCTEMP_LHS_1_idx_0 ) ) )
(assert (=> PCTEMP_LHS_1 (= PCTEMP_LHS_1_len_0 (Length PCTEMP_LHS_1_idx_0) ) ) )
(assert (=> PCTEMP_LHS_1 (< PCTEMP_LHS_1_len_0 15 ) ) )

(check-sat)
(get-model)

