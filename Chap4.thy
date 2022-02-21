theory Chap4
imports Main Chap3_1 Chap3_3
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}"
| "set (Node l a r) = {a} \<union> set l \<union> set r"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True"
| "ord (Node l a r) = (ord l \<and> ord r \<and> (\<forall>x\<in>set l. x \<le> a) \<and> (\<forall>x\<in>set r. a \<le> x))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins a Tip = Node Tip a Tip"
| "ins a (Node l b r) = (
  if a < b then Node (ins a l) b r 
  else if a = b then Node l b r 
  else Node l b (ins a r))"

lemma ins_set: "set (ins a t) = {a} \<union> set t"
  apply (induction t)
  by auto
lemma "ord t \<Longrightarrow> ord (ins a t)"
  apply (induction t rule: ins.induct)
  using ins_set by auto

lemma "\<forall>x. \<exists>y. x = y"
  by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
  by auto

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys@ys; us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n+n"
  (* apply auto *)
  by fastforce

lemma 
  assumes a1: "\<forall>x y. T x y \<or> T y x"
  assumes a2: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  assumes a3: "\<forall>x y. T x y \<longrightarrow> A x y"
  shows "\<forall>x y. A x y \<longrightarrow> T x y"
  apply (rule allI; rule allI)
  apply (rule impI)
  using a1 apply (erule_tac x=x in allE)
  apply (erule_tac x=y in allE)
  apply (erule disjE)
   apply assumption
  using a3 apply (erule_tac x=y in allE)
  apply (erule_tac x=x in allE)
  apply (erule impE)
   apply assumption
  using a2 apply (erule_tac x=x in allE)
  apply (erule_tac x=y in allE)
  apply (erule impE)
   apply (rule conjI)
    apply assumption+
  apply (rule_tac a=x and b=y in forw_subst)
   apply assumption
  apply (drule_tac a=x and b=y in back_subst)
   apply assumption
  apply (drule_tac P="T y" and s=x in subst)
  by assumption+

lemma 
  assumes a1: "\<forall>x y. T x y \<or> T y x"
  assumes a2: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  assumes a3: "\<forall>x y. T x y \<longrightarrow> A x y"
  shows "\<forall>x y. A x y \<longrightarrow> T x y"
  using a1 a2 a3 
  (* apply simp *)
  (* apply auto *)
  (* by fastforce *)
  by blast

lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"
  (* using append_eq_conv_conj *)
  (* apply simp *)
  (* apply auto *)
  (* apply fastforce *)
  (* apply blast *)
  text \<open>using sledgehammer\<close>
  (* using append_eq_append_conv by blast *)
  by (metis append_eq_conv_conj)

thm conjI[of "a=b" "False"]
thm conjI[of _ "False"]
thm conjI[where ?P="a=b" and ?Q="False"]

lemma "\<lbrakk> (a::nat) \<le> b; b \<le> c; c \<le> d; d \<le> e \<rbrakk> \<Longrightarrow> a \<le> e"
  by (blast intro: le_trans)

thm conjI[OF refl[of "a"] refl[of "b"]]
thm refl[of "a"]
thm conjI

lemma "Suc (Suc (Suc a)) \<le> b \<Longrightarrow> a \<le> b"
  thm Suc_leD
  by (blast dest: Suc_leD)

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0"
| evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma "ev m \<Longrightarrow> evn m"
  apply (induction rule: ev.induct)
  by auto

lemma "ev m \<Longrightarrow> ev (m-2)"
  apply (induction rule: ev.induct)
  using ev0 apply simp
  by simp

thm evSS[OF evSS[OF ev0]]

lemma "ev (Suc (Suc (Suc (Suc 0))))"
  apply (rule evSS)
  apply (rule evSS)
  apply (rule ev0)
  done

lemma "evn n \<Longrightarrow> ev n"
  apply (induction n rule: evn.induct)
  by (simp_all add: ev0 evSS)

declare ev.intros[simp,intro]

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
   apply assumption
  by (metis step)

inductive palindrome :: "'a list \<Rightarrow> bool" where
empty: "palindrome []"
| singleton: "palindrome [x]"
| extend: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply (induction rule: palindrome.induct)
  by auto

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x"
| step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma f1: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
  by (auto intro: star'.intros)

lemma "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
   apply (simp add: refl')
  using f1 by force

lemma f2: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
  by (auto intro: star.intros)

lemma "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
   apply (simp add: refl)
  using f2 by force

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
"iter r 0 x x"
| "iter r n y z \<Longrightarrow> r x y \<Longrightarrow> iter r (n+1) x z"

lemma "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
  apply (induction rule: star.induct)
  using iter.intros(1) apply force
  apply clarsimp
  using iter.intros(2) by force

datatype alphabet = a | b

inductive S :: "alphabet list \<Rightarrow> bool" where
"S []"
| "S w \<Longrightarrow> S (a#w@[b])"
| "S v \<Longrightarrow> S w \<Longrightarrow> S (v@w)"

inductive T :: "alphabet list \<Rightarrow> bool" where
"T []"
| "T v \<Longrightarrow> T w \<Longrightarrow> T (v@[a]@w@[b])"

lemma stinduct1:
  assumes "\<And>v. T v \<Longrightarrow> T (v @ u')"
shows "T u' \<Longrightarrow> T v' \<Longrightarrow> T w' \<Longrightarrow> T ((w' @ u') @ [a] @ v' @ [b])"
  using T.intros(2) assms by presburger

lemma stinduct: "T w \<Longrightarrow> T v \<Longrightarrow> T (v @ w)"
  apply (induction w arbitrary: v rule: T.induct)
   apply simp_all
  using stinduct1 by auto

lemma st: "S w \<Longrightarrow> T w"
  apply (induction rule: S.induct)
  using T.intros apply force+
  using stinduct by auto

lemma ts: "T w \<Longrightarrow> S w"
  apply (induction rule: T.induct)
  using S.intros apply force
  by (simp add: S.intros(2) S.intros(3))

lemma "S w = T w"
  using st ts by auto

inductive aval_rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
"aval_rel (N n) s n"
| "aval_rel (V v) s (s v)"
| "aval_rel e1 s x1 \<Longrightarrow> aval_rel e2 s x2 \<Longrightarrow> aval_rel (Plus e1 e2) s (x1 + x2)"

lemma relfn1:
"(\<And>x. Chap4.aval_rel e1 s x \<Longrightarrow> aval e1 s = x) \<Longrightarrow>
       (\<And>x. Chap4.aval_rel e2 s x \<Longrightarrow> aval e2 s = x) \<Longrightarrow>
       Chap4.aval_rel (Plus e1 e2) s x \<Longrightarrow> aval (Plus e1 e2) s = x"
  apply (cases "Plus e1 e2" s x rule: aval_rel.cases)
  by auto

lemma relfn: "aval_rel e s x \<Longrightarrow> aval e s = x"
  apply (induction e arbitrary: x)
  using Chap4.aval_rel.cases apply auto[2]
  using relfn1 by blast

lemma fnrel: "aval e s = x \<Longrightarrow> aval_rel e s x"
  apply (induction e arbitrary: x)
  using Chap4.aval_rel.intros by auto

lemma "aval e s = x \<longleftrightarrow> aval_rel e s x"
  using relfn fnrel by blast

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
"ok n [] n"
| "ok (Suc m) is n \<Longrightarrow> ok m (LOADI k#is) n"
| "ok (Suc m) is n \<Longrightarrow> ok m (LOAD x#is) n"
| "ok (Suc m) is n \<Longrightarrow> ok (Suc (Suc m)) (ADD#is) n"

lemma "ok n is n' \<Longrightarrow> length stk = n \<Longrightarrow> length (exec is s stk) = n'"
  apply (induction arbitrary: stk rule: ok.induct)
     apply simp_all
  apply (subgoal_tac "\<exists>i j stk'. stk = i#j#stk'")
   apply force
  by (metis Suc_length_conv)

end