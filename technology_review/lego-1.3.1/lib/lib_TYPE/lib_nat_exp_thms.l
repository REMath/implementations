(*begin Time-stamp: <02 Nov 97 tms /home/tms/lib/libs/lib_nat/lib_nat_exp_thms.l> @*)

Module lib_nat_exp_thms Import lib_nat_times_thms;

Goal exp_one : {n:nat}Eq (exp n one) n;
intros; 
Refine Eq_trans; Refine +1 times_commutes;
Refine Eq_sym; 
Refine times_one;
Save;

