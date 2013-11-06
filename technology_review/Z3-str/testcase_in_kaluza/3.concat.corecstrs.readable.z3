(declare-variable  T_3  bool)
(declare-variable  T_4  bool)
%------------
%------------
(declare-variable  var_0xINPUT_2  String)
(declare-variable  T2_2  String)
(declare-variable  T2_6  String)
(declare-variable  T_2  String)
(declare-variable  T1_6  String)
(declare-variable  T1_2  String)
(declare-variable  PCTEMP_LHS_1  String)

%============================================

(assert (= PCTEMP_LHS_1 (Concat T1_2 T2_2) ) )
(assert (= T2_2 "=Online" ) )
(assert (= T1_2 var_0xINPUT_2 ) )
(assert (= T_2 (Concat T1_6 T2_6) ) )
(assert (= T2_6 "Now" ) )
(assert (= T1_6 PCTEMP_LHS_1 ) )
(assert (= T_3 (not (=  T_2 "Hello=Joe=OnlineNow")) ) )
(assert (= T_4 (not T_3 ) ) )
(assert T_4)

(check-sat)
(get-model)

