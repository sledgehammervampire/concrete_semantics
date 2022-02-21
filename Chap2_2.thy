theory Chap2_2
  imports Main
begin

datatype nat = Z | Suc nat

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add Z n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_b: "add n Z = n"
  apply (induction n)
   apply (rule add.simps(1))
  apply (subst add.simps(2))
  apply (subst nat.inject)
  apply assumption
  done

lemma add_i:
  assumes f1: "\<And>m. add m n = add n m"
  shows "add m (Suc n) = add (Suc n) m"
  apply (induction m)
   apply (subst add.simps(1))
   apply (rule add_b[symmetric])
  apply (subst (1 2) add.simps(2))
  apply (subst nat.inject)
  apply (subst f1[symmetric])
  apply (subst add.simps(2))
  apply (subst f1)
  apply (subst add.simps(2)[symmetric])
  by assumption

lemma add_comm: "add m n = add n m"
  apply (induction n arbitrary: m)
   apply (subst add.simps(1))
   apply (rule add_b)
  apply (erule add_i)
  done

value "1 + (2::Nat.nat)"

value "1 + (2::int)"

value "1 - (2::Nat.nat)"

value "1 - (2::int)"

lemma add_assoc: "add (add l m) n = add l (add m n)"
  apply (induction l)
  by simp+

fun double :: "nat \<Rightarrow> nat" where
"double Z = Z"
| "double (Suc n) = Suc (Suc (double n))"

lemma double_add: "double n = add n n"
  apply (induction n)
   apply simp+
  apply (subst (2) add_comm)
  by simp

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> Nat.nat" where
"count [] y = 0"
| "count (x#xs) y = (if x = y then 1 else 0) + count xs y"

lemma count_leq_len: "count xs y \<le> length xs"
  apply (induction xs)
  by simp+

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] y = [y]"
| "snoc (x#xs) y = x#(snoc xs y)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []"
| "rev (x#xs) = snoc (rev xs) x"

lemma rev_snoc: "rev (snoc xs x) = x#(rev xs)"
  apply (induction xs)
   apply simp
  apply (subst snoc.simps)
  apply (subst rev.simps)
  apply (rule_tac a="rev (snoc xs x)" and b="x#rev xs" in forw_subst)
   apply assumption
  apply (subst snoc.simps)
  apply (subst rev.simps)
  by (rule refl)

lemma rev_inv: "rev (rev xs) = xs"
  apply (induction xs)
   apply simp
  by (simp add: rev_snoc)

fun sum_upto :: "Nat.nat \<Rightarrow> Nat.nat" where
"sum_upto 0 = 0"
| "sum_upto (Nat.Suc n) = n + 1 + sum_upto n"

lemma "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
   apply simp
  apply (subst sum_upto.simps)
  apply (rule_tac a="sum_upto n" and b="n * (n+1) div 2" in forw_subst)
  by simp+

end
