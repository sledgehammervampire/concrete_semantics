theory Chap3_2
imports Main Chap3_1
begin

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc b) s = b"
| "bval (Not e) s = (\<not>bval e s)"
| "bval (And e1 e2) s = (bval e1 s \<and> bval e2 s)"
| "bval (Less e1 e2) s = (aval e1 s < aval e2 s)"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False"
| "not (Bc False) = Bc True"
| "not b = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b"
| "and b (Bc True) = b"
| "and (Bc False) b = Bc False"
| "and b (Bc False) = Bc False"
| "and b1 b2 = And b1 b2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = Bc (n1 < n2)"
| "less a1 a2 = Less a1 a2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc b) = Bc b"
| "bsimp (Not e) = not (bsimp e)"
| "bsimp (And e1 e2) = and (bsimp e1) (bsimp e2)"
| "bsimp (Less e1 e2) = less (asimp e1) (asimp e2)"

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a1 a2 = And (Not (Less a1 a2)) (Not (Less a2 a1))"

lemma "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  by auto

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a1 a2 = Not (Less a2 a1)"

lemma "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  by auto

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 b) s = b"
| "ifval (If e1 e2 e3) s = (if ifval e1 s then ifval e2 s else ifval e3 s)"
| "ifval (Less2 e1 e2) s = (aval e1 s < aval e2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc b) = Bc2 b"
| "b2ifexp (Not e) = If (b2ifexp e) (Bc2 False) (Bc2 True)"
| "b2ifexp (And e1 e2) = If (b2ifexp e1) (b2ifexp e2) (Bc2 False)"
| "b2ifexp (Less e1 e2) = Less2 e1 e2"

definition Implies :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Implies e1 e2 = Not (And e1 (Not e2))"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 b) = Bc b"
| "if2bexp (If e1 e2 e3) = 
    And (Implies (if2bexp e1) (if2bexp e2)) (Implies (Not (if2bexp e1)) (if2bexp e3))"
| "if2bexp (Less2 e1 e2) = Less e1 e2"

lemma "bval (if2bexp e) s = ifval e s"
  apply (induction e)
  by (auto simp add: Implies_def)

lemma "ifval (b2ifexp e) s = bval e s"
  apply (induction e)
  by auto

datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x" |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR _) = True"
| "is_nnf (NOT (VAR _)) = True"
| "is_nnf (NOT _) = False"
| "is_nnf (AND e1 e2) = (is_nnf e1 \<and> is_nnf e2)"
| "is_nnf (OR e1 e2) = (is_nnf e1 \<and> is_nnf e2)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR x) = VAR x"
| "nnf (AND e1 e2) = AND (nnf e1) (nnf e2)"
| "nnf (OR e1 e2) = OR (nnf e1) (nnf e2)"
| "nnf (NOT (VAR x)) = NOT (VAR x)"
| "nnf (NOT (NOT e)) = nnf e"
| "nnf (NOT (AND e1 e2)) = OR (nnf (NOT e1)) (nnf (NOT e2))"
| "nnf (NOT (OR e1 e2)) = AND (nnf (NOT e1)) (nnf (NOT e2))"

lemma "pbval (nnf e) s = pbval e s"
  apply (induction e rule: nnf.induct)
  by auto

lemma "is_nnf (nnf e)"
  apply (induction e rule: nnf.induct)
  by auto

fun without_OR :: "pbexp \<Rightarrow> bool" where
"without_OR (VAR _) = True"
| "without_OR (NOT e) = without_OR e"
| "without_OR (AND e1 e2) = (without_OR e1 \<and> without_OR e2)"
| "without_OR (OR _ _) = False"

fun is_dnf_helper :: "pbexp \<Rightarrow> bool" where
"is_dnf_helper (VAR _) = True"
| "is_dnf_helper (NOT e) = is_dnf_helper e"
| "is_dnf_helper (AND e1 e2) = without_OR (AND e1 e2)"
| "is_dnf_helper (OR e1 e2) = (is_dnf_helper e1 \<and> is_dnf_helper e2)"

definition is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf e = (is_nnf e \<and> is_dnf_helper e)"

lemma "(P \<or> Q) \<and> (R \<or> S)"
  apply (subst conj_disj_distribL)
  apply (subst (1 2) conj_disj_distribR)
  oops

fun dnfify :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"dnfify (OR e1 e2) e = OR (dnfify e1 e) (dnfify e2 e)"
| "dnfify e (OR e1 e2) = OR (dnfify e e1) (dnfify e e2)"
| "dnfify e1 e2 = AND e1 e2"

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR x) = VAR x"
| "dnf_of_nnf (NOT e) = NOT e"
| "dnf_of_nnf (OR e1 e2) = OR (dnf_of_nnf e1) (dnf_of_nnf e2)"
| "dnf_of_nnf (AND e1 e2) = dnfify (dnf_of_nnf e1) (dnf_of_nnf e2)"

lemma dnfify_and: "pbval (dnfify e1 e2) s = (pbval e1 s \<and> pbval e2 s)"
  apply (induction rule: dnfify.induct)
  by auto

lemma "pbval (dnf_of_nnf b) s = pbval b s"
  apply (induction b rule: dnf_of_nnf.induct)
     apply simp+
  using dnfify_and by blast

lemma dnfify_nnf: "\<lbrakk> is_nnf e1; is_nnf e2 \<rbrakk> \<Longrightarrow> is_nnf (dnfify e1 e2)"
  apply (induction e1 e2 rule: dnfify.induct)
  by auto

lemma dnf_of_nnf_is_nnf: "is_nnf b \<Longrightarrow> is_nnf (dnf_of_nnf b)"
  apply (induction b)
     apply simp_all
  using dnfify_nnf by blast

lemma dnfify_is_dnf_helper: 
"\<lbrakk> is_dnf e1; is_dnf e2 \<rbrakk> \<Longrightarrow> is_dnf_helper (dnfify e1 e2)"
  apply (induction e1 e2 rule: dnfify.induct)
  unfolding is_dnf_def by (auto elim: is_nnf.elims)

lemma dnf_of_nnf_is_dnf_helper: "is_nnf b \<Longrightarrow> is_dnf_helper (dnf_of_nnf b)"
  apply (induction b rule: dnf_of_nnf.induct)
  using dnfify_is_dnf_helper dnf_of_nnf_is_nnf unfolding is_dnf_def 
  by (auto elim: is_nnf.elims)

lemma "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
  unfolding is_dnf_def apply safe
  using dnf_of_nnf_is_nnf dnf_of_nnf_is_dnf_helper by auto
   
end