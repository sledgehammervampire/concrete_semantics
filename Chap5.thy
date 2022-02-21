theory Chap5 imports Main
begin
lemma "\<not>surj (f::'a \<Rightarrow> 'a set)"
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

end