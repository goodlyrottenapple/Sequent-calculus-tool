theory SequentCalculusEq
imports Main SequentCalculus "../src/isabelle/SequentCalc_SE"
begin


fun structure_to_formula_list :: "Structure \<Rightarrow> Formula list" where
"structure_to_formula_list (f \<^sub>S) = [f]"|
"structure_to_formula_list (X ,\<^sub>S Y) = (structure_to_formula_list X) ; (structure_to_formula_list Y)" |
"structure_to_formula_list _ = []"


fun sequentCalc_SE_to_sequentCalculus :: "Sequent \<Rightarrow> sequent" (">> _") where
"sequentCalc_SE_to_sequentCalculus (X \<turnstile>\<^sub>S Y) = structure_to_formula_list X \<turnstile> structure_to_formula_list Y" |
"sequentCalc_SE_to_sequentCalculus _ = [] \<turnstile> []"

fun formula_list_to_structure :: "Formula list \<Rightarrow> Structure" where
"formula_list_to_structure [] = I"|
"formula_list_to_structure [x] = (x \<^sub>S)"|
"formula_list_to_structure (x#xs) = Structure_Comma (x \<^sub>S) (formula_list_to_structure xs)"


lemma formula_list_to_structure_simp1a: "Y \<noteq> [] \<Longrightarrow> formula_list_to_structure ([A] ; Y) = (A \<^sub>S) ,\<^sub>S formula_list_to_structure Y" 
unfolding formula_list_to_structure.simps
by (metis SequentCalculus.concat_def append_Cons append_self_conv2 formula_list_to_structure.simps(3) list.exhaust_sel)

lemma formula_list_to_structure_simp1b: "Y = [] \<Longrightarrow> formula_list_to_structure ([A] ; Y) = (A \<^sub>S)"
by (simp add: SequentCalculus.concat_def)

fun sequentCalculus_to_sequentCalc_SE :: "sequent \<Rightarrow> Sequent" ("<< _") where
"sequentCalculus_to_sequentCalc_SE (X \<turnstile> Y) = formula_list_to_structure X \<turnstile>\<^sub>S formula_list_to_structure Y"

lemma P_L''_1: "\<turnstile>D ((X1 ; [A]) ; (B ; X2) \<turnstile> Y) \<Longrightarrow> \<turnstile>D ((X1 ; B) ; ([A] ; X2) \<turnstile> Y)"
proof (induct B arbitrary: X1 X2 A)
case Nil thus ?case
by (simp add: SequentCalculus.concat_def)
next
case (Cons b B) 
have subst1: "((X1 ; [b]) ; [A]) ; (B ; X2) = (X1 ; [b]) ; ([A] ; (B ; X2))"
by (simp add: SequentCalculus.concat_def)
have "\<turnstile>D ((X1 ; [b]) ; [A]) ; (B ; X2) \<turnstile> Y"
apply(subst subst1)
apply(rule_tac derivable'.P_L)
using Cons(2) by (simp add: SequentCalculus.concat_def)
with Cons(1) have "\<turnstile>D ((X1 ; [b]) ; B) ; ([A] ; X2) \<turnstile> Y" by simp

thus ?case by (simp add: SequentCalculus.concat_def)
qed


lemma P_L': "\<turnstile>D ((X1 ; A) ; (B ; X2) \<turnstile> Y) \<Longrightarrow> \<turnstile>D ((X1 ; B) ; (A ; X2) \<turnstile> Y)"
proof (induct A)
case Nil thus ?case
by (simp add: SequentCalculus.concat_def)
next
case (Cons a A) thus ?case
proof (induct B)
case Nil thus ?case
by (simp add: SequentCalculus.concat_def)
next
case (Cons b B)

 thus ?case


lemma P_R': "\<turnstile>D (X \<turnstile> (Y1 ; A) ; (B ; Y2)) \<Longrightarrow> \<turnstile>D (X \<turnstile> (Y1 ; B) ; (A ; Y2))" sorry

lemma sequentCalculus_to_sequentCalc_SE_derivable:
fixes loc
assumes "loc \<turnstile>d seq"
  and "loc = []"
  shows "\<turnstile>D (>> seq)"
using assms apply (induct loc seq)
unfolding sequentCalc_SE_to_sequentCalculus.simps structure_to_formula_list.simps
apply(auto intro:derivable'.intros)
using P_L' apply simp
using SequentCalculus.concat_def apply(auto intro:derivable'.intros)
using derivable'.C_L apply auto[1]
using P_R' apply simp
done


end