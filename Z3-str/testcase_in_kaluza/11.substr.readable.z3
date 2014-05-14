(declare-variable  T_2  bool)
%------------
(declare-variable  I2_2  Int)
(declare-variable  I0_2  Int)
(declare-variable  I1_2  Int)
%------------
(declare-variable  T3_2  String)
(declare-variable  T2_2  String)
(declare-variable  var_0xINPUT_2  String)
(declare-variable  T1_2  String)
(declare-variable  PCTEMP_LHS_1  String)

%============================================

(assert (= I0_2 (- 1 0) ) )
(assert  (>= 0 0 ) )
(assert  (>= 1 0 ) )
(assert  (<= 1 I1_2 ) )
(assert (= I2_2 I1_2 ) )
(assert (= I0_2 (Length PCTEMP_LHS_1) ) )
(assert (= var_0xINPUT_2 (Concat T1_2 T2_2) ) )
(assert (= T2_2 (Concat PCTEMP_LHS_1 T3_2) ) )
(assert (= 0 (Length T1_2) ) )
(assert (= I1_2 (Length var_0xINPUT_2) ) )
(assert (= T_2 (not (=  PCTEMP_LHS_1 "hello")) ) )
(assert T_2)

(check-sat)
(get-model)

