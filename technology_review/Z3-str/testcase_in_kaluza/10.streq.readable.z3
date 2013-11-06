(declare-variable  T_2  bool)
(declare-variable  T_4  bool)
(declare-variable  T_5  bool)
%------------
(declare-variable  I2_2  Int)
(declare-variable  I0_2  Int)
(declare-variable  I1_2  Int)
%------------
(declare-variable  T3_2  String)
(declare-variable  var_0xINPUT_19  String)
(declare-variable  T2_2  String)
(declare-variable  T1_2  String)
(declare-variable  PCTEMP_LHS_1  String)

%============================================

(assert (= I0_2 (- 5 0) ) )
(assert  (>= 0 0 ) )
(assert  (>= 5 0 ) )
(assert  (<= 5 I1_2 ) )
(assert (= I2_2 I1_2 ) )
(assert (= I0_2 (Length PCTEMP_LHS_1) ) )
(assert (= var_0xINPUT_19 (Concat T1_2 T2_2) ) )
(assert (= T2_2 (Concat PCTEMP_LHS_1 T3_2) ) )
(assert (= 0 (Length T1_2) ) )
(assert (= I1_2 (Length var_0xINPUT_19) ) )
(assert (= T_2 (= PCTEMP_LHS_1 "Hello") ) )
(assert T_2)
(assert (= T_4 (= PCTEMP_LHS_1 "hello") ) )
(assert (= T_5 (not T_4 ) ) )
(assert T_5)

(check-sat)
(get-model)

