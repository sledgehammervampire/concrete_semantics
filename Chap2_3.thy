theory Chap2_3
imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []"
| "contents (Node l a r) = a # contents l @ contents r"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0"
| "sum_tree (Node l a r) = a + sum_tree l + sum_tree r"

lemma "sum_tree t = sum_list (contents t)"
  apply (induction t)
  by auto

definition pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order t = contents t"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []"
| "post_order (Node l a r) = post_order l @ post_order r @ [a]"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip"
| "mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "pre_order (mirror t) = rev (post_order t)"
  apply (induction t)
  by (auto simp add: pre_order_def)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []"
| "intersperse a [x] = [x]"
| "intersperse a (x#y#xs) = x#a#y#(intersperse a xs)"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
  by simp+

end