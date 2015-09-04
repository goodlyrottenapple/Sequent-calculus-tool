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
"formula_list_to_structure (x#xs) = Structure_Comma (x \<^sub>S) (formula_list_to_structure xs)"


fun sequentCalculus_to_sequentCalc_SE :: "sequent \<Rightarrow> Sequent" ("<< _") where
"sequentCalculus_to_sequentCalc_SE (X \<turnstile> Y) = formula_list_to_structure X \<turnstile>\<^sub>S formula_list_to_structure Y"

lemma P_L'': "\<turnstile>D ((X1 ; [A]) ; (B ; X2) \<turnstile> Y) \<Longrightarrow> \<turnstile>D ((X1 ; B) ; ([A] ; X2) \<turnstile> Y)"
proof (induct B arbitrary: X1 X2 A)
case Nil 
  thus ?case
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
proof (induct A arbitrary: X1 B X2)
case Nil 
  thus ?case
  by (simp add: SequentCalculus.concat_def)
next
case (Cons a A)
  have " \<turnstile>D (X1 ; A) ; ([a]; (B ; X2)) \<turnstile> Y"
  apply(rule_tac P_L'')
  using Cons(2) by (simp add: SequentCalculus.concat_def)
  then have " \<turnstile>D (X1 ; A) ; (([a];B) ; X2) \<turnstile> Y" by (simp add: SequentCalculus.concat_def)
  with Cons(1) have 1: "\<turnstile>D (X1 ; ([a];B)) ; (A ; X2) \<turnstile> Y" by simp
  have subst1: "(X1 ; B) ; ((a # A) ; X2) = (X1 ; B) ; ([a]; (A ; X2))" by (simp add: SequentCalculus.concat_def)
  show ?case
  apply(subst subst1)
  apply(rule_tac P_L'')
  using 1 by (simp add: SequentCalculus.concat_def)
qed

lemma P_R'': "\<turnstile>D (Y \<turnstile> (X1 ; [A]) ; (B ; X2)) \<Longrightarrow> \<turnstile>D (Y \<turnstile> (X1 ; B) ; ([A] ; X2))"
proof (induct B arbitrary: X1 X2 A)
case Nil 
  thus ?case
  by (simp add: SequentCalculus.concat_def)
next
case (Cons b B) 
  have subst1: "((X1 ; [b]) ; [A]) ; (B ; X2) = (X1 ; [b]) ; ([A] ; (B ; X2))"
  by (simp add: SequentCalculus.concat_def)
  have "\<turnstile>D Y \<turnstile> ((X1 ; [b]) ; [A]) ; (B ; X2)"
  apply(subst subst1)
  apply(rule_tac derivable'.P_R)
  using Cons(2) by (simp add: SequentCalculus.concat_def)
  with Cons(1) have "\<turnstile>D Y  \<turnstile> ((X1 ; [b]) ; B) ; ([A] ; X2)" by simp
  thus ?case by (simp add: SequentCalculus.concat_def)
qed

lemma P_R': "\<turnstile>D (Y \<turnstile> (X1 ; A) ; (B ; X2)) \<Longrightarrow> \<turnstile>D (Y \<turnstile> (X1 ; B) ; (A ; X2))"
proof (induct A arbitrary: X1 B X2)
case Nil 
  thus ?case
  by (simp add: SequentCalculus.concat_def)
next
case (Cons a A)
  have " \<turnstile>D Y \<turnstile> (X1 ; A) ; ([a]; (B ; X2))"
  apply(rule_tac P_R'')
  using Cons(2) by (simp add: SequentCalculus.concat_def)
  then have " \<turnstile>D Y \<turnstile> (X1 ; A) ; (([a];B) ; X2)" by (simp add: SequentCalculus.concat_def)
  with Cons(1) have 1: "\<turnstile>D Y \<turnstile> (X1 ; ([a];B)) ; (A ; X2)" by simp
  have subst1: "(X1 ; B) ; ((a # A) ; X2) = (X1 ; B) ; ([a]; (A ; X2))" by (simp add: SequentCalculus.concat_def)
  show ?case
  apply(subst subst1)
  apply(rule_tac P_R'')
  using 1 by (simp add: SequentCalculus.concat_def)
qed

lemma sequentCalc_SE_to_sequentCalculus_derivable:
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
using P_R' by simp


lemma formula_list_to_structure_der_P_L': 
  assumes "loc \<turnstile>d A ,\<^sub>S formula_list_to_structure ([X] ; Y) \<turnstile>\<^sub>S Z" 
  shows "loc \<turnstile>d A ,\<^sub>S formula_list_to_structure (Y ; [X]) \<turnstile>\<^sub>S Z"
using assms 
proof(induction Y arbitrary: X A)
case Nil
  have subst1: "[] ; [X] = [X]" by (simp add: SequentCalculus.concat_def)
  show ?case
  apply(subst subst1)
  using Nil by (simp add: SequentCalculus.concat_def)
next
case (Cons Y Ys)
  have subst1: "[X] ; Ys = X # Ys" by (simp add: SequentCalculus.concat_def)

  have "loc \<turnstile>d (A ,\<^sub>S (Y \<^sub>S)) ,\<^sub>S formula_list_to_structure ([X] ;  Ys) \<turnstile>\<^sub>S Z" 
  apply (subst subst1)
  apply simp
  apply(rule_tac derivable.P_L)
  using Cons(2) by (simp add: A_L2 SequentCalculus.concat_def)
  with Cons(1) have 1: "loc \<turnstile>d (A ,\<^sub>S (Y \<^sub>S)) ,\<^sub>S formula_list_to_structure (Ys ; [X]) \<turnstile>\<^sub>S Z" by simp
  have subst2: "(Y # Ys) ; [X] = Y # (Ys ; [X])" by (simp add: SequentCalculus.concat_def)

  show ?case
  apply (subst subst2)
  apply simp
  apply(rule_tac derivable.A_L)
  using 1 by simp
qed




lemma formula_list_to_structure_der_P_L'2: 
  assumes "loc \<turnstile>d A ,\<^sub>S formula_list_to_structure (Y ; [X]) \<turnstile>\<^sub>S Z" 
  shows "loc \<turnstile>d A ,\<^sub>S formula_list_to_structure ([X] ; Y) \<turnstile>\<^sub>S Z"
using assms 
proof(induction Y arbitrary: X A)
case Nil
  have subst1: "[X] ; [] = [X]" by (simp add: SequentCalculus.concat_def)
  show ?case
  apply(subst subst1)
  using Nil by (simp add: SequentCalculus.concat_def)
next
case (Cons Y Ys)
  from Cons(2) have "loc \<turnstile>d (A ,\<^sub>S (Y \<^sub>S)) ,\<^sub>S formula_list_to_structure (Ys ; [X]) \<turnstile>\<^sub>S Z" by (simp add: A_L2 SequentCalculus.concat_def)
  with Cons(1) have 1: "loc \<turnstile>d (A ,\<^sub>S (Y \<^sub>S)) ,\<^sub>S formula_list_to_structure ([X] ; Ys) \<turnstile>\<^sub>S Z" by simp
  have subst1: " [X] ; (Y # Ys) = X # (Y #Ys)" by (simp add: SequentCalculus.concat_def)

  show ?case
  apply (subst subst1)
  apply simp
  apply(rule_tac derivable.A_L)
  apply(rule_tac derivable.P_L)
  using 1 by (simp add: SequentCalculus.concat_def)
qed

lemma formula_list_to_structure_der_P_L: 
  assumes "loc \<turnstile>d A ,\<^sub>S formula_list_to_structure (X ; Y) \<turnstile>\<^sub>S Z" 
  shows "loc \<turnstile>d A ,\<^sub>S formula_list_to_structure (Y ; X) \<turnstile>\<^sub>S Z"
using assms 
proof(induction Y arbitrary: X A)
case Nil
have subst1: "[] ; X = X" by (simp add: SequentCalculus.concat_def)
  show ?case
  apply(subst subst1)
  using Nil by (simp add: SequentCalculus.concat_def)
next
case (Cons Y Ys)
  then have "loc \<turnstile>d A ,\<^sub>S formula_list_to_structure ((X ; [Y]) ; Ys) \<turnstile>\<^sub>S Z" by (simp add: SequentCalculus.concat_def)
  with Cons(1) have 1: "loc \<turnstile>d A ,\<^sub>S formula_list_to_structure (Ys ; (X ; [Y])) \<turnstile>\<^sub>S Z" by simp
  have subst1: "(Y # Ys) ; X = [Y] ; (Ys ; X)" by (simp add: SequentCalculus.concat_def)
  show ?case
  apply(subst subst1)
  apply(rule formula_list_to_structure_der_P_L'2)
  using 1 by (simp add: SequentCalculus.concat_def)
qed


lemma formula_list_to_structure_der_P_R'2: 
  assumes "loc \<turnstile>d Z \<turnstile>\<^sub>S A ,\<^sub>S formula_list_to_structure (Y ; [X])" 
  shows "loc \<turnstile>d Z \<turnstile>\<^sub>S A ,\<^sub>S formula_list_to_structure ([X] ; Y)"
using assms 
proof(induction Y arbitrary: X A)
case Nil
  have subst1: "[X] ; [] = [X]" by (simp add: SequentCalculus.concat_def)
  show ?case
  apply(subst subst1)
  using Nil by (simp add: SequentCalculus.concat_def)
next
case (Cons Y Ys)
  from Cons(2) have "loc \<turnstile>d Z \<turnstile>\<^sub>S (A ,\<^sub>S (Y \<^sub>S)) ,\<^sub>S formula_list_to_structure (Ys ; [X])" by (simp add: A_R2 SequentCalculus.concat_def)
  with Cons(1) have 1: "loc \<turnstile>d Z \<turnstile>\<^sub>S (A ,\<^sub>S (Y \<^sub>S)) ,\<^sub>S formula_list_to_structure ([X] ; Ys)" by simp
  have subst1: "[X] ; (Y # Ys) = X # (Y #Ys)" by (simp add: SequentCalculus.concat_def)

  show ?case
  apply (subst subst1)
  apply simp
  apply(rule_tac derivable.A_R)
  apply(rule_tac derivable.P_R)
  using 1 by (simp add: SequentCalculus.concat_def)
qed


lemma formula_list_to_structure_der_P_R: 
  assumes "loc \<turnstile>d Z  \<turnstile>\<^sub>S A ,\<^sub>S formula_list_to_structure (X ; Y)" 
  shows "loc \<turnstile>d Z  \<turnstile>\<^sub>S A ,\<^sub>S formula_list_to_structure (Y ; X)"
using assms 
proof(induction Y arbitrary: X A)
case Nil
have subst1: "[] ; X = X" by (simp add: SequentCalculus.concat_def)
  show ?case
  apply(subst subst1)
  using Nil by (simp add: SequentCalculus.concat_def)
next
case (Cons Y Ys)
  then have "loc \<turnstile>d Z  \<turnstile>\<^sub>S A ,\<^sub>S formula_list_to_structure ((X ; [Y]) ; Ys)" by (simp add: SequentCalculus.concat_def)
  with Cons(1) have 1: "loc \<turnstile>d Z  \<turnstile>\<^sub>S A ,\<^sub>S formula_list_to_structure (Ys ; (X ; [Y]))" by simp
  have subst1: "(Y # Ys) ; X = [Y] ; (Ys ; X)" by (simp add: SequentCalculus.concat_def)
  show ?case
  apply(subst subst1)
  apply(rule formula_list_to_structure_der_P_R'2)
  using 1 by (simp add: SequentCalculus.concat_def)
qed



lemma formula_list_to_structure_der_simp1: 
  assumes "loc \<turnstile>d A ,\<^sub>S ((formula_list_to_structure X) ,\<^sub>S (formula_list_to_structure Y)) \<turnstile>\<^sub>S Z"
  shows "loc \<turnstile>d A ,\<^sub>S formula_list_to_structure (X ; Y) \<turnstile>\<^sub>S Z"
using assms proof(induct Y arbitrary: X A)
case Nil
  have subst1: "\<And>Y. Y ; [] = Y" by (simp add: SequentCalculus.concat_def)
  show ?case 
  apply (subst subst1)
  using Nil by (metis A_L2 I_L_R formula_list_to_structure.simps(1))
next
case (Cons Y Ys)
  have subst1: "X ; (Y # Ys) = X;(Y#Ys)" by (simp add: SequentCalculus.concat_def)
  have subst2: "(Y # Ys) ; X = Y # (Ys ; X)" by (simp add: SequentCalculus.concat_def)
  
  have "loc \<turnstile>d (A ,\<^sub>S (Y \<^sub>S)) ,\<^sub>S (formula_list_to_structure X ,\<^sub>S formula_list_to_structure Ys) \<turnstile>\<^sub>S Z"

  apply(rule_tac derivable.P_L)
  apply(rule_tac derivable.A_L2)
  using Cons(2) by simp
  
  with Cons(1) have 1: "loc \<turnstile>d (A ,\<^sub>S (Y \<^sub>S)) ,\<^sub>S formula_list_to_structure (X ; Ys) \<turnstile>\<^sub>S Z" by simp
  show ?case
  apply(subst subst1)
  apply(rule formula_list_to_structure_der_P_L)
  apply(subst subst2)
  apply simp
  apply (rule derivable.A_L)
  apply(rule formula_list_to_structure_der_P_L)
  using 1 using SequentCalculus.concat_def by auto
qed

lemma formula_list_to_structure_der_simp1r[simp]: "loc \<turnstile>d (formula_list_to_structure X) ,\<^sub>S (Y \<^sub>S) \<turnstile>\<^sub>S Z \<Longrightarrow> loc \<turnstile>d formula_list_to_structure (X ; [Y]) \<turnstile>\<^sub>S Z" 
by (metis A_L I_L_L I_L_L2 I_L_R2 formula_list_to_structure.simps(1) formula_list_to_structure.simps(2) formula_list_to_structure_der_simp1)

lemma formula_list_to_structure_der_simp1l[simp]: "loc \<turnstile>d (X \<^sub>S) ,\<^sub>S (formula_list_to_structure Y) \<turnstile>\<^sub>S Z \<Longrightarrow> loc \<turnstile>d formula_list_to_structure ([X] ; Y) \<turnstile>\<^sub>S Z"
by (simp add: SequentCalculus.concat_def)


lemma formula_list_to_structure_der_simp1b: 
  assumes "loc \<turnstile>d A ,\<^sub>S formula_list_to_structure (X ; Y) \<turnstile>\<^sub>S Z" 
  shows "loc \<turnstile>d A ,\<^sub>S ((formula_list_to_structure X) ,\<^sub>S (formula_list_to_structure Y)) \<turnstile>\<^sub>S Z"
using assms 
proof(induction Y arbitrary: X A)
case Nil
  show ?case 
  apply simp
  apply(rule_tac derivable.A_L)
  apply(rule_tac derivable.I_L_R2)
  using Nil by (simp add: SequentCalculus.concat_def)
next
case (Cons Y Ys)
  have subst1: "(Y # X) ; Ys = Y # (X ; Ys)" using SequentCalculus.concat_def by auto
  have subst2: "(Y \<^sub>S) ,\<^sub>S formula_list_to_structure (Ys ; X) = formula_list_to_structure ((Y#Ys) ; X)" using SequentCalculus.concat_def by auto
  have "loc \<turnstile>d A ,\<^sub>S formula_list_to_structure ((Y # X) ; Ys) \<turnstile>\<^sub>S Z"
  apply (subst subst1)
  apply simp
  apply(rule_tac derivable.A_L)
  apply (rule formula_list_to_structure_der_P_L)
  apply(rule_tac derivable.A_L2)
  apply (subst subst2)
  apply (rule formula_list_to_structure_der_P_L)
  using Cons by simp
  
  with Cons have 1: "loc \<turnstile>d A ,\<^sub>S (formula_list_to_structure (Y # X) ,\<^sub>S formula_list_to_structure Ys) \<turnstile>\<^sub>S Z" by blast
  show ?case
  apply simp
  apply(rule_tac derivable.A_L)
  apply(rule_tac derivable.P_L)
  apply(rule_tac derivable.A_L2)
  using 1 by (simp add: A_L A_L2 Cons.IH Cons.prems formula_list_to_structure_der_P_L subst2)
qed

lemma formula_list_to_structure_der_simp1br[simp]: "loc \<turnstile>d formula_list_to_structure (X ; [Y]) \<turnstile>\<^sub>S Z \<Longrightarrow> loc \<turnstile>d (formula_list_to_structure X) ,\<^sub>S (Y \<^sub>S) \<turnstile>\<^sub>S Z"
by (metis A_L2 I_L_L I_L_L2 I_L_R formula_list_to_structure.simps(1) formula_list_to_structure.simps(2) formula_list_to_structure_der_simp1b)

lemma formula_list_to_structure_der_simp1bl[simp]: "loc \<turnstile>d formula_list_to_structure ([X] ; Y) \<turnstile>\<^sub>S Z \<Longrightarrow> loc \<turnstile>d (X \<^sub>S) ,\<^sub>S (formula_list_to_structure Y) \<turnstile>\<^sub>S Z"
by (simp add: SequentCalculus.concat_def)




lemma formula_list_to_structure_der_simp2: 
  assumes "loc \<turnstile>d Z \<turnstile>\<^sub>S A ,\<^sub>S (formula_list_to_structure X ,\<^sub>S formula_list_to_structure Y)"
  shows "loc \<turnstile>d Z \<turnstile>\<^sub>S A ,\<^sub>S formula_list_to_structure (X ; Y)"
using assms proof(induct Y arbitrary: X A)
case Nil
  have subst1: "\<And>Y. Y ; [] = Y" by (simp add: SequentCalculus.concat_def)
  show ?case 
  apply (subst subst1)
  using Nil by (metis A_R2 I_R_R formula_list_to_structure.simps(1))
next
case (Cons Y Ys)
  have subst1: "X ; (Y # Ys) = X;(Y#Ys)" by (simp add: SequentCalculus.concat_def)
  have subst2: "(Y # Ys) ; X = Y # (Ys ; X)" by (simp add: SequentCalculus.concat_def)
  
  have "loc \<turnstile>d Z \<turnstile>\<^sub>S  (A ,\<^sub>S (Y \<^sub>S)) ,\<^sub>S (formula_list_to_structure X ,\<^sub>S formula_list_to_structure Ys)"

  apply(rule_tac derivable.P_R)
  apply(rule_tac derivable.A_R2)

  using Cons(2) by simp

  with Cons(1) have 1: "loc \<turnstile>d Z \<turnstile>\<^sub>S  (A ,\<^sub>S (Y \<^sub>S)) ,\<^sub>S formula_list_to_structure (X ; Ys)" by simp
  show ?case
  apply(subst subst1)
  apply(rule formula_list_to_structure_der_P_R)
  apply(subst subst2)
  apply simp
  apply(rule_tac derivable.A_R)
  apply(rule formula_list_to_structure_der_P_R)
  using 1 using SequentCalculus.concat_def by auto
qed



lemma formula_list_to_structure_der_simp2l[simp]: "loc \<turnstile>d X \<turnstile>\<^sub>S (A \<^sub>S) ,\<^sub>S formula_list_to_structure Y \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S formula_list_to_structure ([A] ; Y)"
by (simp add: SequentCalculus.concat_def)

lemma formula_list_to_structure_der_simp2r[simp]: "loc \<turnstile>d X \<turnstile>\<^sub>S formula_list_to_structure Y ,\<^sub>S (A \<^sub>S) \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S formula_list_to_structure (Y ; [A])"
by (metis A_R I_R_L I_R_L2 I_R_R2 formula_list_to_structure.simps(1) formula_list_to_structure.simps(2) formula_list_to_structure_der_simp2)

lemma formula_list_to_structure_der_simp2b:
  assumes "loc \<turnstile>d Z \<turnstile>\<^sub>S A ,\<^sub>S formula_list_to_structure (X ; Y)"
  shows "loc \<turnstile>d Z \<turnstile>\<^sub>S A ,\<^sub>S (formula_list_to_structure X ,\<^sub>S formula_list_to_structure Y)"
using assms 
proof(induction Y arbitrary: X A)
case Nil
  show ?case 
  apply simp
  apply(rule_tac derivable.A_R)
  apply(rule_tac derivable.I_R_R2)
  using Nil by (simp add: SequentCalculus.concat_def)
next
case (Cons Y Ys)
  have subst1: "(Y # X) ; Ys = Y # (X ; Ys)" using SequentCalculus.concat_def by auto
  have subst2: "(Y \<^sub>S) ,\<^sub>S formula_list_to_structure (Ys ; X) = formula_list_to_structure ((Y#Ys) ; X)" using SequentCalculus.concat_def by auto
  have "loc \<turnstile>d Z \<turnstile>\<^sub>S (A ,\<^sub>S (Y \<^sub>S)) ,\<^sub>S formula_list_to_structure (X ; Ys)"
  apply (rule formula_list_to_structure_der_P_R)
  apply(rule_tac derivable.A_R2)
  apply (subst subst2)
  apply (rule formula_list_to_structure_der_P_R)
  using Cons by simp

  then show ?case
  apply simp
  apply(rule_tac derivable.A_R)
  apply(rule_tac derivable.P_R)
  apply(rule_tac derivable.A_R2)
  apply(rule_tac derivable.A_R)
  using Cons by (simp add: Cons.IH A_R2 subst1)
qed

lemma formula_list_to_structure_der_simp2bl[simp]:"loc \<turnstile>d X \<turnstile>\<^sub>S formula_list_to_structure ([A] ; Y) \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S (A \<^sub>S) ,\<^sub>S formula_list_to_structure Y"
by (simp add: SequentCalculus.concat_def)

lemma formula_list_to_structure_der_simp2br[simp]:"loc \<turnstile>d X \<turnstile>\<^sub>S formula_list_to_structure (Y ; [A]) \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S formula_list_to_structure Y ,\<^sub>S (A \<^sub>S)"
by (metis A_R2 I_R_L I_R_L2 I_R_R formula_list_to_structure.simps(1) formula_list_to_structure.simps(2) formula_list_to_structure_der_simp2b)

lemma dP_L' : "[] \<turnstile>d X ,\<^sub>S Y \<turnstile>\<^sub>S Z \<Longrightarrow> [] \<turnstile>d Y ,\<^sub>S X \<turnstile>\<^sub>S Z"
apply(rule_tac derivable.I_L_L)
apply(rule_tac derivable.A_L)
apply(rule_tac derivable.I_L_R)
apply(rule_tac derivable.A_L2)
apply(rule_tac derivable.P_L)
apply(rule_tac derivable.A_L)
apply(rule_tac derivable.I_L_R2)
apply(rule_tac derivable.A_L2)
apply(rule_tac derivable.I_L_L2)
by simp


lemma dP_R' : "[] \<turnstile>d Z \<turnstile>\<^sub>S X ,\<^sub>S Y \<Longrightarrow> [] \<turnstile>d Z \<turnstile>\<^sub>S Y ,\<^sub>S X"
apply(rule_tac derivable.I_R_L)
apply(rule_tac derivable.A_R)
apply(rule_tac derivable.I_R_R)
apply(rule_tac derivable.A_R2)
apply(rule_tac derivable.P_R)
apply(rule_tac derivable.A_R)
apply(rule_tac derivable.I_R_R2)
apply(rule_tac derivable.A_R2)
apply(rule_tac derivable.I_R_L2)
by simp


lemma subst_C_L : "(A \<^sub>S) ,\<^sub>S ((A \<^sub>S) ,\<^sub>S I) = formula_list_to_structure [A, A]" by simp

lemma sequentCalculus_to_sequentCalc_SE_derivable:
fixes loc
assumes "\<turnstile>D seq"
  shows "[] \<turnstile>d (<< seq)"
using assms apply (induct seq)
unfolding sequentCalculus_to_sequentCalc_SE.simps formula_list_to_structure.simps

apply(rule_tac formula_list_to_structure_der_simp1r)
apply(rule_tac derivable.Not_L)
apply(rule_tac formula_list_to_structure_der_simp2bl)
apply simp

apply(rule_tac formula_list_to_structure_der_simp1r)
apply(rule_tac derivable.And_L_1)
apply(rule_tac formula_list_to_structure_der_simp1br)
apply simp

apply(rule_tac formula_list_to_structure_der_simp1r)
apply(rule_tac derivable.And_L_2)
apply(rule_tac formula_list_to_structure_der_simp1br)
apply simp

apply(rule_tac formula_list_to_structure_der_simp2l)
apply(rule_tac derivable.ImpR_R)
apply(rule_tac formula_list_to_structure_der_simp2bl)
apply(rule_tac formula_list_to_structure_der_simp1br)
apply blast

apply(rule_tac formula_list_to_structure_der_simp1r)
apply(rule dP_L')
apply(rule_tac formula_list_to_structure_der_simp1)
apply(rule dP_L')
apply(rule_tac derivable.I_R_L)
apply(rule_tac formula_list_to_structure_der_simp2)
apply(rule_tac derivable.I_R_L2)
apply(rule_tac derivable.Or_L)
apply(rule_tac formula_list_to_structure_der_simp1br)
apply simp+

apply(rule_tac formula_list_to_structure_der_simp2l)
apply(rule_tac derivable.Not_R)
apply(rule_tac formula_list_to_structure_der_simp1br)
apply simp

apply(rule_tac formula_list_to_structure_der_simp1r)
apply(rule dP_L')
apply(rule_tac formula_list_to_structure_der_simp1)
apply(rule dP_L')
apply(rule_tac derivable.I_R_L)
apply(rule_tac formula_list_to_structure_der_simp2)
apply(rule_tac derivable.I_R_L2)
apply(rule_tac derivable.ImpR_L)
apply(rule_tac formula_list_to_structure_der_simp1br)
apply simp+


apply(rule_tac formula_list_to_structure_der_simp2l)
apply(rule_tac derivable.I_L_L)
apply(rule_tac formula_list_to_structure_der_simp1)
apply(rule_tac derivable.I_L_L2)
apply(rule_tac formula_list_to_structure_der_simp2)
apply(rule_tac derivable.And_R)
apply(rule_tac formula_list_to_structure_der_simp2bl)
apply simp+

apply(rule_tac formula_list_to_structure_der_simp2l)
apply(rule_tac derivable.Or_R_2)
apply(rule_tac formula_list_to_structure_der_simp2bl)
apply simp

apply(rule_tac formula_list_to_structure_der_simp2l)
apply(rule_tac derivable.Or_R_1)
apply(rule_tac formula_list_to_structure_der_simp2bl)
apply simp

apply(rule_tac formula_list_to_structure_der_simp1r)
apply(rule_tac derivable.W_L)
apply simp

apply(rule_tac derivable.I_L_L)
apply(rule_tac formula_list_to_structure_der_simp1)
apply(rule_tac derivable.I_L_L2)
apply(rule_tac formula_list_to_structure_der_simp1)
apply(rule dP_L')
apply(rule_tac formula_list_to_structure_der_simp1)
apply(rule dP_L')
apply(rule_tac derivable.P_L)
apply(rule_tac formula_list_to_structure_der_simp1b)
apply(rule dP_L')
apply(rule_tac formula_list_to_structure_der_simp1b)
apply(rule dP_L')
apply(rule_tac derivable.I_L_L)
apply(rule_tac formula_list_to_structure_der_simp1b)
apply(rule_tac derivable.I_L_L2)
apply simp


apply(rule_tac formula_list_to_structure_der_simp1r)
apply(rule_tac derivable.C_L)
apply(rule_tac derivable.A_L)
apply(rule_tac derivable.I_L_R)
apply(rule_tac derivable.A_L2)
apply(rule_tac derivable.A_L2)
apply(subst subst_C_L)
apply(rule_tac derivable.I_L_L)
apply(rule_tac formula_list_to_structure_der_simp1b)
apply(rule_tac derivable.I_L_L2)
using SequentCalculus.concat_def apply auto[1]


apply(rule_tac formula_list_to_structure_der_simp2l)
apply(rule_tac derivable.C_R)
apply(rule dP_R')
apply(rule_tac derivable.A_R)
apply(rule_tac derivable.I_R_R)
apply(rule_tac derivable.A_R2)
apply(rule_tac derivable.A_R2)
apply(subst subst_C_L)
apply(rule dP_R')
apply(rule_tac derivable.I_R_L)
apply(rule_tac formula_list_to_structure_der_simp2b)
apply(rule_tac derivable.I_R_L2)
using SequentCalculus.concat_def apply auto[1]

apply(rule_tac derivable.I_R_L)
apply(rule_tac formula_list_to_structure_der_simp2)
apply(rule_tac derivable.I_R_L2)
apply(rule_tac formula_list_to_structure_der_simp2)
apply(rule dP_R')
apply(rule_tac formula_list_to_structure_der_simp2)
apply(rule dP_R')
apply(rule_tac derivable.P_R)
apply(rule_tac formula_list_to_structure_der_simp2b)
apply(rule dP_R')
apply(rule_tac formula_list_to_structure_der_simp2b)
apply(rule dP_R')
apply(rule_tac derivable.I_R_L)
apply(rule_tac formula_list_to_structure_der_simp2b)
apply(rule_tac derivable.I_R_L2)
apply simp

apply(rule_tac formula_list_to_structure_der_simp2l)
apply(rule_tac derivable.W_R)
apply simp

by (simp add: I_L_R2 I_R_R2 derivable.Id)


end