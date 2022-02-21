theory Chap2_5
imports Main
begin

datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 0"
| "nodes (Node l r) = nodes l + nodes r"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t"
| "explode (Suc n) t = explode n (Node t t)"

lemma "nodes (explode n t) = nodes t * 2^n"
  apply (induction n arbitrary: t)
  by auto

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x"
| "eval (Const a) x = a"
| "eval (Add e1 e2) x = eval e1 x + eval e2 x"
| "eval (Mult e1 e2) x = eval e1 x * eval e2 x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] a = 0"
| "evalp (x#xs) a = x + a * evalp xs a"

fun padd :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"padd [] q = q"
| "padd p [] = p"
| "padd (p0#p) (q0#q) = (p0+q0)#(padd p q)"

fun cmul :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"cmul c p = map ((*) c) p"

fun xmul :: "int list \<Rightarrow> int list" where
"xmul p = 0#p"

fun pmul :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"pmul [] q = []"
| "pmul (p0#p) q = padd (cmul p0 q) (xmul (pmul p q))"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]"
| "coeffs (Const a) = [a]"
| "coeffs (Add e1 e2) = padd (coeffs e1) (coeffs e2)"
| "coeffs (Mult e1 e2) = pmul (coeffs e1) (coeffs e2)"

lemma evalp_add: "evalp (padd p q) x = evalp p x + evalp q x"
  apply (induction rule: padd.induct)
  by (simp add: algebra_simps)+

lemma evalp_cmul: "evalp (cmul c p) x = c * evalp p x"
  apply (induction p)
  by (simp add: algebra_simps)+

lemma evalp_xmul: "evalp (xmul p) x = x * evalp p x"
  apply (induction p)
  by (simp add: algebra_simps)+

lemma evalp_mul: "evalp (pmul p q) x = evalp p x * evalp q x"
  apply (induction rule: pmul.induct)
   apply simp
  apply (simp only: pmul.simps)
  apply (simp only: evalp_add)
  apply (simp only: evalp_cmul evalp_xmul evalp.simps)
  by (simp only: algebra_simps)

lemma "evalp (coeffs e) x = eval e x"
  apply (induction e)
     apply simp+
  using evalp_add evalp_mul by auto

end