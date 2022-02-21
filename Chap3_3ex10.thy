theory Chap3_3ex10
  imports 
Main 
Chap3_1 
Chap3_2 
"HOL-Library.Monad_Syntax"
begin

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk = Some (n#stk)"
| "exec1 (LOAD x) s stk = Some ((s x)#stk)"
| "exec1 ADD s (x#y#stk) = Some ((y+x)#stk)"
| "exec1 ADD _ _ = None"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some stk"
| "exec (i#is) s stk = (case exec1 i s stk of
  None \<Rightarrow> None
  | Some stk' \<Rightarrow> exec is s stk'
)"

definition exec' :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec' is s stk = fold (\<lambda>i stko. stko \<bind> exec1 i s) is (Some stk)"

lemma exec_None: "None = fold (\<lambda>i stko. stko \<bind> exec1 i s) is None"
  apply (induction "is")
  using [[simp_trace]]
  by simp+

lemma "exec is s stk = exec' is s stk"
  apply (induction "is" arbitrary: stk)
  unfolding exec'_def using exec_None 
  by (auto split: option.split)

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]"
| "comp (V x) = [LOAD x]"
| "comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma comp_concat:
"exec (is1 @ is2) s stk = exec is1 s stk \<bind> exec is2 s"
  apply (induction is1 arbitrary: stk)
  by (auto split: option.split)

lemma "exec (comp a) s stk = Some stk \<bind> Some \<circ> ((#) (aval a s))"
  apply (induction a arbitrary: stk)
  using comp_concat by auto

end