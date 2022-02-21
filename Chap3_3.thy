theory Chap3_3
imports Main Chap3_1 Chap3_2
begin

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = n#stk"
| "exec1 (LOAD x) s stk = (s x)#stk"
| "exec1 ADD s (x#y#stk) = (y+x)#stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk"
| "exec (i#is) s stk = exec is s (exec1 i s stk)"

definition exec' :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec' is s stk = fold (\<lambda>i stk'. exec1 i s stk') is stk"

definition exec'' :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec'' is s stk = foldr (\<lambda>i stk'. exec1 i s stk') is stk"

lemma "exec is s stk = exec' is s stk"
  apply (induction "is" arbitrary: stk)
  unfolding exec'_def by simp+

lemma "exec is s stk = exec'' is s stk"
  oops

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]"
| "comp (V x) = [LOAD x]"
| "comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma exec_concat:
"exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  apply (induction is1 arbitrary: stk)
  by simp+

lemma "exec (comp a) s stk = aval a s # stk"
  apply (induction a arbitrary: stk)
    apply simp+
  using exec_concat by simp

end