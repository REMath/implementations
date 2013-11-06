(declare-variable  T_2  bool)
(declare-variable  T_SELECT_1  bool)
(declare-variable  T_3  bool)
%------------
(declare-variable  I0_2  Int)
(declare-variable  PCTEMP_LHS_1  Int)
%------------
(declare-variable  T3_2  String)
(declare-variable  T4_2  String)
(declare-variable  var_0xINPUT_2  String)
(declare-variable  T0_2  String)
(declare-variable  T2_2  String)
(declare-variable  T5_2  String)
(declare-variable  T1_2  String)

%============================================

(assert (= T_SELECT_1 (not (=  PCTEMP_LHS_1 (- 0 1))) ) )
(assert (=> T_SELECT_1 (= PCTEMP_LHS_1 (+ I0_2 0) ) ) )
(assert (=> T_SELECT_1 (= var_0xINPUT_2 (Concat T0_2 T1_2) ) ) )
(assert (=> T_SELECT_1 (= I0_2 (Length T4_2) ) ) )
(assert (=> T_SELECT_1 (= 0 (Length T0_2) ) ) )
(assert (=> T_SELECT_1 (= T1_2 (Concat T2_2 T3_2) ) ) )
(assert (=> T_SELECT_1 (= T2_2 (Concat T4_2 T5_2) ) ) )
(assert (=> T_SELECT_1 (= T5_2 "=" ) ) )
(assert (=> (not T_SELECT_1) (= PCTEMP_LHS_1 (- 0 1) ) ) )
(assert (=> (not T_SELECT_1) (= var_0xINPUT_2 (Concat T0_2 T1_2) ) ) )
(assert (=> (not T_SELECT_1) (= 0 (Length T0_2) ) ) )
(assert (= T_2 (not (=  PCTEMP_LHS_1 1)) ) )
(assert (= T_3 (not T_2 ) ) )
(assert T_3)

(check-sat)
(get-model)

