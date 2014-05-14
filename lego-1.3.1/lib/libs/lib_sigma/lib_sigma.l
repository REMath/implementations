Module lib_sigma Import lib_eq_basics;

Inductive [sigma:SET] ElimOver TYPE
Parameters [A|SET][B|A->SET]
Constructors [dep_pair:{a:A}{b:B a}sigma];

sigma_rec == [T|TYPE] sigma_elim ([_:sigma]T);

sigma_ind == [P:sigma->Prop] sigma_elim P;

sig_pi1 == sigma_rec [a:A][_:(B a)]a;

sig_pi2 == sigma_elim ([x:sigma](B (sig_pi1 x))) [a:A][b:(B a)]b;

Goal dep_pair_eta : {x:sigma}(Eq x (dep_pair (sig_pi1 x) (sig_pi2 x)));
intros x;
Refine sigma_ind [x:sigma]Eq x (dep_pair (sig_pi1 x) (sig_pi2 x));
intros a b;
Refine Eq_refl;
Save dep_pair_eta;

Goal sig_pi1_inj : {x,y:sigma}(Eq x y) -> (Eq (sig_pi1 x) (sig_pi1 y));
intros x y H;
Refine Eq_resp sig_pi1;
Refine H;
Save sig_pi1_inj;



Discharge A;

Sigma [A:SET][B:A->SET] == sigma|A|B;

(* product types *)
[Prod [A,B:SET] = Sigma A [_:A]B];
[Pr [A,B|SET] = dep_pair|A|[_:A]B];
