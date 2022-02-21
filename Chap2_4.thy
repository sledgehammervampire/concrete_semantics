theory Chap2_4
imports Main
begin

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys"
| "itrev (x#xs) ys = itrev xs (x#ys)"

lemma itrev_rev: "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
  by auto
lemma "itrev xs [] = rev xs"
  by (simp add: itrev_rev)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n"
| "itadd (Suc m) n = itadd m (Suc n)"

lemma "itadd m n = m + n"
  apply (induction m arbitrary: n)
  by auto

end