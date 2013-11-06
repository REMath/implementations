(declare-variable  T_2  bool)
(declare-variable  T_SELECT_1  bool)
%------------
(declare-variable  PCTEMP_LHS_1  Int)
%------------
(declare-variable  T3_2  String)
(declare-variable  T2_2  String)
(declare-variable  var_0xINPUT_2  String)
(declare-variable  T1_2  String)
(declare-variable  T0_2  String)

%============================================

(assert (= T_SELECT_1 (not (=  PCTEMP_LHS_1 (- 0 1))) ) )
(assert (=> T_SELECT_1 (= var_0xINPUT_2 (Concat T0_2 T1_2) ) ) )
(assert (=> T_SELECT_1 (= T1_2 (Concat T2_2 T3_2) ) ) )
(assert (=> T_SELECT_1 (= PCTEMP_LHS_1 (Length T0_2) ) ) )
(assert (=> (not T_SELECT_1) (= PCTEMP_LHS_1 (- 0 1) ) ) )
(assert (= T_2 (= PCTEMP_LHS_1 1) ) )
(assert T_2)

(check-sat)
(get-model)

