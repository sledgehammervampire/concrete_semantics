theory Chap5 imports Main
begin   
lemma "\<not>  surj (f::'a \<Rightarrow> 'a set)"
proof  
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by (simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

lemma "\<not>surj (f::'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  from this show False by blast
qed

lemma "\<not>surj (f::'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  thus "False" by blast
qed

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "\<exists>a. {x. x \<notin> f x} = f a" using s by (auto simp: surj_def)
  thus ?thesis by blast
qed

lemma "\<not>surj (f::'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<in> f a \<longleftrightarrow> a \<notin> f a" by blast
  thus "False" by blast
qed

lemma "R"
proof cases
  assume P
  show R sorry
next
  assume "\<not>P"
  show R sorry
qed

lemma assumes "P \<or> Q" shows R
  using assms
proof
  assume P
  show R sorry
next
  assume Q
  show R sorry
qed

lemma "P \<longleftrightarrow> Q"
proof
  assume P show Q sorry
next
  assume Q show P sorry
qed

lemma "P"
proof (rule ccontr)
  assume "\<not>P"
  show "False" sorry
qed

lemma "\<forall>x. P x"
proof
  fix y
  show "P y" sorry
qed

lemma "(A::'a set) = B"
proof
  show "A\<le>B" sorry
next
  show "B\<le>A" sorry
qed

lemma "(A::'a set) \<le> B"
proof
  fix x
  assume "x \<in> A"
  show "x \<in> B" sorry
qed

lemma "formula\<^sub>1 \<longleftrightarrow> formula\<^sub>2" (is "?L \<longleftrightarrow> ?R")
proof
  assume "?L"
  show "?R" sorry
next
  assume "?R"
  show "?L" sorry
qed

lemma "\<forall>(x::nat). x \<ge> 0"
proof
  fix x :: nat
  have "x \<ge> 0" sorry
  from `x \<ge> 0` show "x \<ge> 0" sorry
qed

lemma P
proof -
  have P1 sorry
  moreover have P2 sorry
  ultimately have P3 sorry
  thus P sorry
qed

lemma fixes a b :: int assumes "b dvd (a+b)" shows "b dvd a"
proof -
  have "\<exists>k'. a = b*k'" if asm: "a+b = b*k" for k
  proof
    show "a = b*(k-1)" using asm by (simp add: algebra_simps)
  qed
  then show ?thesis using assms by (auto simp add: dvd_def)
qed

lemma assumes T: "\<forall>x y. T x y \<or> T y x"
and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
proof (rule disjE[of "T x y" "T y x"])
  show "T x y \<or> T y x" using T by blast
next
  show "T x y \<Longrightarrow> T x y" by assumption
next
  assume 1: "T y x"
  hence "A y x" using TA by blast
  hence "x = y" using A assms by blast
  thus "T x y" using 1 by blast
qed

lemma "\<exists>ys zs. xs = ys@zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof -
  obtain k r where f1: "length xs = 2*k + r" and f2: "r = 0 \<or> r = 1" 
    by (metis bot_nat_0.not_eq_extremum mod2_gr_0 mult_div_mod_eq)
  let ?ys = "take (k+r) xs" and ?zs = "drop (k+r) xs"
  have "length ?ys = k+r" and "length ?zs = k" using f1 by auto
  hence "length ?ys = length ?zs \<or> length ?ys = length ?zs + 1" using f2 by simp
  moreover have "xs = ?ys@?zs" by simp
  ultimately show ?thesis by blast
qed

lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []"
  thus ?thesis by simp
next
  fix y ys assume "xs = y#ys"
  thus ?thesis by simp
qed

lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  then show ?thesis by simp
qed

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P (Suc n)" by simp
qed

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0"
| evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n"
proof (induction rule: ev.induct)
  case ev0
  then show ?case by simp
next
  case evSS
  thus ?case by simp
qed

lemma "ev n \<Longrightarrow> evn n"
proof (induction rule: ev.induct)
  case ev0
  then show ?case by simp
next
  case (evSS n)
  thm evSS.IH
  thm evSS.hyps
  thm evSS.prems
  then have "evn (Suc (Suc n)) = evn n" by simp
  thus ?case using \<open>evn n\<close> by blast
qed

lemma "ev n \<Longrightarrow> ev (n-2)"
proof -
  assume "ev n"
  thus "ev (n-2)"
  proof cases
    case ev0
    then show ?thesis by (simp add: ev.ev0)
  next
    case (evSS n)
    then show ?thesis by (simp add: ev.evSS)
  qed
qed

lemma "ev (Suc 0) \<Longrightarrow> P"
proof -
  assume "ev (Suc 0)" then show "P" by cases
qed

lemma "\<not>ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  from this have "ev (Suc 0)" by cases
  thus False by cases
qed

fun P :: "nat \<Rightarrow> bool" where
"P (Suc n) = (\<not>ev n)"
| "P _ = True"

lemma "ev n \<Longrightarrow> P n \<Longrightarrow> \<not> ev (Suc n)"
proof (cases n)
  case 0
  then show ?thesis sorry
next
  case (Suc nat)
  then show ?thesis sorry
qed
   
lemma "ev (Suc m) \<Longrightarrow>
P 0 \<Longrightarrow> (\<And>n. ev n \<Longrightarrow> P n \<Longrightarrow> P (Suc (Suc n))) \<Longrightarrow> P (Suc m)"
  apply simp
  oops

lemma "ev (Suc m) \<Longrightarrow> \<not>ev m"
  thm ev.induct[where x="Suc m" and P=P]
proof (induction "Suc m" arbitrary: m rule: ev.induct)
  fix n assume IH: "\<And>m. n = Suc m \<Longrightarrow> \<not>ev m"
  show "\<not>ev (Suc n)"
  proof
    assume "ev (Suc n)"
    thus False
    proof cases
      fix k assume "n = Suc k" "ev k"
      thus False using IH by auto
    qed
  qed
qed

lemma 
  assumes "ev (Suc (Suc n))"
  shows "ev n"
  using assms
proof cases
  assume "ev n" thus "ev n" by blast
qed

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
"iter r 0 x x"
| "iter r n y z \<Longrightarrow> r x y \<Longrightarrow> iter r (n+1) x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case (1 x)
  show ?case using refl by force
next
  case (2 n y z x)
  from 2(2) 2(3) show ?case using step by force
qed

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}"
| "elems (x#xs) = insert x (elems xs)"

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  hence False by simp
  thus ?case by blast
next
  case (Cons a xs)
  show ?case
  proof (cases "x = a")
    case True
    hence "a # xs = [] @ x # xs" by simp
    moreover have "x \<notin> elems []" by simp
    ultimately show ?thesis by blast
  next
    case False
    then obtain ys zs where "xs = ys @ x # zs" and 1: "x \<notin> elems ys"
      using Cons by auto
    hence "a # xs = (a#ys) @ x # zs" by simp
    moreover have "x \<notin> elems (a#ys)" using False 1 by simp
    ultimately show ?thesis by blast
  qed
qed

datatype alphabet = a | b
inductive S :: "alphabet list \<Rightarrow> bool" where
"S []"
| "S w \<Longrightarrow> S (a#w@[b])"
| "S v \<Longrightarrow> S w \<Longrightarrow> S (v@w)"

fun balanced :: "nat \<Rightarrow> alphabet list \<Rightarrow> bool" where
"balanced 0 [] = True"
| "balanced (Suc n) [] = False"
| "balanced n (a#xs) = balanced (Suc n) xs"
| "balanced 0 (b#xs) = False"
| "balanced (Suc n) (b#xs) = balanced n xs"

lemma balanced1: "S (replicate n a) \<Longrightarrow> n > 0 \<Longrightarrow> False"
proof (induction "replicate n a" arbitrary: n rule: S.induct)
  case 1
  then show ?case by simp
next
  case (2 w)
  then show ?case
    by (metis alphabet.distinct(1) append_is_Nil_conv bot_nat_0.not_eq_extremum last.simps last_replicate last_snoc list.distinct(1))
next
  case (3 v w)
  then obtain n' n'' where f1: "v = replicate n' a" and f2: "w = replicate n'' a"
    by (metis map_eq_append_conv map_replicate_const map_replicate_trivial)
  have "n' = 0 \<Longrightarrow> n'' = 0 \<Longrightarrow> False" using 3 f1 by simp
  hence "n' > 0 \<or> n'' > 0" by blast
  then show ?case using 3 f1 f2 by blast
qed

lemma balanced6:
  assumes a1: "v \<noteq> []" and a2: "S v" and a3: "S w" 
  and a4: "v @ w = replicate n a @ xs"
  shows "\<exists>ys. v = replicate n a @ ys"
proof -
  have "\<not>(\<exists>v'. v@v' = replicate n a)"
  proof
    assume "\<exists>v'. v @ v' = replicate n a"
    then obtain n' where f1: "v = replicate n' a" and f2: "n' > 0"
      by (metis a1 gr_zeroI list.simps(8) list.size(3) map_eq_append_conv map_replicate_const map_replicate_trivial)
    have "S v \<Longrightarrow> False" using f1 balanced1 f2 by blast
    then show "False" using a2 by simp
  qed
  thus ?thesis
    by (meson a4 append_eq_append_conv2)
qed

lemma balanced2: "S (replicate n a @ xs) \<Longrightarrow> S (replicate (Suc n) a @ b # xs)"
proof (induction "replicate n a @ xs" arbitrary: n xs rule: S.induct)
  case 1
  then show ?case using S.intros(1) S.intros(2) by force
next
  case (2 w)
  then show ?case
  proof (cases n)
    assume f1: "n = 0"
    hence "S xs" using 2 S.intros by force
    moreover have "S [a, b]" using S.intros by force
    ultimately have "S ([a, b] @ xs)" using S.intros 2 by force
    hence "S (replicate (Suc 0) a @ b # xs)" by simp
    thus ?thesis using f1 by simp
  next
    case (Suc nat)
    then obtain xs' where f1: "w = replicate nat a @ xs'" using 2(3)
      by (metis alphabet.distinct(1) append.right_neutral append_Cons butlast_append list.sel(3) replicate_Suc replicate_append_same snoc_eq_iff_butlast) 
    with 2(2) have "S (replicate (Suc nat) a @ b # xs')" by simp
    moreover have "xs = xs'@[b]" using 2(3) f1 Suc by simp
    ultimately show ?thesis using Suc S.intros by force
  qed
next
  case (3 v w)
  show ?case
  proof (cases v)
    case Nil
    then show ?thesis using 3 S.intros by force
  next
    case Cons
    with 3(1,3,5) obtain ys where f1: "v = replicate n a @ ys"
      using balanced6 by blast
    hence "S (replicate (Suc n) a @ b # ys)" using 3 by blast
    moreover have "replicate (Suc n) a @ b # xs = replicate (Suc n) a @ b # ys @ w"
      using 3 f1 by force
    ultimately show ?thesis using 3 by (metis S.intros(3) append.assoc append_Cons)
  qed
qed

lemma balanced3: "balanced n w \<Longrightarrow> S (replicate n a @ w)"
proof (induction n w rule: balanced.induct)
  case 1
  then show ?case
    by (simp add: S.intros(1))
next
  case (2 n)
  then show ?case by simp
next
  case (3 n xs)
  hence "balanced (Suc n) xs" by simp
  hence "S (replicate (Suc n) a @ xs)" using 3 by simp
  then show ?case by (simp add: replicate_app_Cons_same)
next                                                       
  case (4 xs)
  then show ?case by simp
next
  case (5 n xs)
  hence "balanced n xs" by simp
  hence "S (replicate n a @ xs)" using 5 by simp
  then show ?case using balanced2 by blast
qed

lemma balanced5: "balanced n w \<Longrightarrow> balanced (Suc n) (w@[b])"
  apply (induction n w rule: balanced.induct)
  by auto

lemma balanced7: "balanced m v \<Longrightarrow> balanced 0 w \<Longrightarrow> balanced m (v@w)"
  apply (induction arbitrary: w rule: balanced.induct)
  by auto

lemma balanced4: "S (replicate n a @ w) \<Longrightarrow> balanced n w"
proof (induction "replicate n a @ w" arbitrary: n w rule: S.induct)
  case 1
  then show ?case by simp
next
  case (2 w')
  then show ?case
  proof (cases n)
    case 0
    hence "balanced 0 w'" using 2 by simp
    hence "balanced 1 (w' @ [b])" using balanced5 by simp
    then show ?thesis using 0 2 by auto
  next
    case (Suc nat)
    then obtain w'' where f1: "w' = replicate nat a @ w''" using 2
      by (metis alphabet.distinct(1) append_Cons append_is_Nil_conv butlast_append butlast_snoc last_snoc list.distinct(1) list.sel(3) replicate_Suc replicate_append_same)
    hence "balanced nat w''" using 2 by simp
    moreover have "w'' @ [b] = w" using Suc 2 f1 by simp
    ultimately show ?thesis using 2 Suc apply clarsimp
      using balanced5 by presburger
  qed
next
  case (3 v' w')
  show ?case
  proof (cases v')
    case Nil
    then show ?thesis using 3 by simp
  next
    case Cons
    hence "v' \<noteq> []" by simp
    then obtain ys where f1: "v' = replicate n a @ ys"
      using 3 balanced6 by meson
    hence "balanced n ys" using 3 by blast
    moreover have "balanced 0 w'" using 3 by simp
    moreover have "ys @ w' = w" using 3 f1 by simp
    ultimately show ?thesis using balanced7 by blast
  qed
qed

lemma "balanced n w = S (replicate n a @ w)"
  using balanced3 balanced4 by blast

end
