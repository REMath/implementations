(declare-variable  T_3  bool)
(declare-variable  T_4  bool)
(declare-variable  PCTEMP_LHS_1  bool)
%------------
%------------
(declare-variable  M1_2  String)
(declare-variable  P1_2  String)
(declare-variable  T0_2  String)
(declare-variable  T2_2  String)
(declare-variable  P0_2  String)
(declare-variable  T_2  String)
(declare-variable  M0_2  String)
(declare-variable  PCTEMP_LHS_1_idx_0  String)
(declare-variable  PCTEMP_LHS_1_idx_1  String)
(declare-variable  PCTEMP_LHS_1_idx_2  String)
(declare-variable  var_0xINPUT_2  String)
(declare-variable  T1_2  String)

%============================================

(assert (= T2_2 PCTEMP_LHS_1_idx_2 ) )
(assert (= T0_2 var_0xINPUT_2 ) )
(assert (= M1_2 "=" ) )
(assert (= P1_2 (Concat PCTEMP_LHS_1_idx_1 M1_2) ) )
(assert (= T1_2 (Concat P1_2 T2_2) ) )
(assert (= M0_2 "=" ) )
(assert (= P0_2 (Concat PCTEMP_LHS_1_idx_0 M0_2) ) )
(assert (= T0_2 (Concat P0_2 T1_2) ) )
(assert PCTEMP_LHS_1)
(assert (=> PCTEMP_LHS_1 (= T_2 PCTEMP_LHS_1_idx_0 ) ) )
(assert (= T_3 (not (=  T_2 "Hello")) ) )
(assert (= T_4 (not T_3 ) ) )
(assert T_4)

(check-sat)
(get-model)

