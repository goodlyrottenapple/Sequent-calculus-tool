theory (*calc_name_se-BEGIN*)SequentCalc_SE(*calc_name_se-END*)
imports Main (*calc_name_core_se-BEGIN*)SequentCalc_Core_SE(*calc_name_core_se-END*)
begin

datatype Locale = (*(*uncommentL?Formula?RuleCut-BEGIN*)*)(*uncommentL?Formula?RuleCut-END*)
                  CutFormula Formula |
                  (*uncommentR?Formula?RuleCut-BEGIN*)(*(*uncommentR?Formula?RuleCut-END*)*)
                  (*(*uncommentL?Sequent-BEGIN*)*)(*uncommentL?Sequent-END*)
                  Premise Sequent |
                  (*uncommentR?Sequent-BEGIN*)(*(*uncommentR?Sequent-END*)*)
                  (*(*uncommentL?Structure-BEGIN*)*)(*uncommentL?Structure-END*)
                  Part Structure |
                  (*uncommentR?Structure-BEGIN*)(*(*uncommentR?Structure-END*)*)
                  (*(*uncommentL?Action?Agent*)
                  RelAKA "Action \<Rightarrow> Agent \<Rightarrow> Action list" | 
                  (*uncommentR?Action?Agent*)*)
                  (*(*uncommentL?Action?Formula*)
                  PreFormula Action Formula |
                  (*uncommentR?Action?Formula*)*)
                  (*(*uncommentL?Agent*)
                  LAgent Agent |
                  (*uncommentR?Agent*)*)
                  Empty


(*(*uncommentL?Atprop?Formula?Formula_Atprop?Formula_Action_Formula*)
fun is_act_mod :: "Structure \<Rightarrow> Atprop option" where
"is_act_mod (Structure_Formula (Formula_Atprop p)) = Some p"|
"is_act_mod (Structure_ForwA _ s) = is_act_mod s"|
"is_act_mod (Structure_BackA _ s) = is_act_mod s"|

"is_act_mod _ = None"

fun atom :: "Sequent \<Rightarrow> bool" where
"atom (l \<turnstile>\<^sub>S r) = ( (is_act_mod l) \<noteq> None \<and> (is_act_mod l) = (is_act_mod r) )"
(*uncommentR?Atprop?Formula?Formula_Atprop?Formula_Action_Formula*)*)


fun pairs :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
"pairs [] [] = []" |
"pairs [] Y = []" |
"pairs X [] = []" |
"pairs (X#Xs) (Y#Ys) = (X, Y)#(pairs Xs Ys)"

(*calc_structure_rules_se-BEGIN*)
inductive derivable :: "Locale list \<Rightarrow> Sequent \<Rightarrow> bool"  (infix "\<turnstile>d" 300) where
SingleCut: "(CutFormula f) \<in> set l \<Longrightarrow> l \<turnstile>d ((X ,\<^sub>S W) \<turnstile>\<^sub>S (Z ,\<^sub>S Y))"
| 
Not_L: "l \<turnstile>d (X \<turnstile>\<^sub>S ((A \<^sub>S) ,\<^sub>S Y)) \<Longrightarrow> l \<turnstile>d ((X ,\<^sub>S ((\<not>\<^sub>F A) \<^sub>S)) \<turnstile>\<^sub>S Y)"|
And_L_1: "l \<turnstile>d ((X ,\<^sub>S (A \<^sub>S)) \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d ((X ,\<^sub>S ((A \<and>\<^sub>F B) \<^sub>S)) \<turnstile>\<^sub>S Z)"|
And_L_2: "l \<turnstile>d ((X ,\<^sub>S (B \<^sub>S)) \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d ((X ,\<^sub>S ((A \<and>\<^sub>F B) \<^sub>S)) \<turnstile>\<^sub>S Z)"|
ImpR_R: "l \<turnstile>d ((Z ,\<^sub>S (A \<^sub>S)) \<turnstile>\<^sub>S ((B \<^sub>S) ,\<^sub>S X)) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S (((A \<rightarrow>\<^sub>F B) \<^sub>S) ,\<^sub>S X))"|
Or_L: "l \<turnstile>d ((Z ,\<^sub>S (B \<^sub>S)) \<turnstile>\<^sub>S W) \<Longrightarrow> l \<turnstile>d ((X ,\<^sub>S (A \<^sub>S)) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (((X ,\<^sub>S Z) ,\<^sub>S ((A \<or>\<^sub>F B) \<^sub>S)) \<turnstile>\<^sub>S (Y ,\<^sub>S W))"|
Not_R: "l \<turnstile>d ((X ,\<^sub>S (A \<^sub>S)) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (((\<not>\<^sub>F A) \<^sub>S) ,\<^sub>S Y))"|
ImpR_L: "l \<turnstile>d ((Z ,\<^sub>S (B \<^sub>S)) \<turnstile>\<^sub>S W) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S ((A \<^sub>S) ,\<^sub>S Y)) \<Longrightarrow> l \<turnstile>d (((X ,\<^sub>S Z) ,\<^sub>S ((A \<rightarrow>\<^sub>F B) \<^sub>S)) \<turnstile>\<^sub>S (Y ,\<^sub>S W))"|
And_R: "l \<turnstile>d (Z \<turnstile>\<^sub>S ((B \<^sub>S) ,\<^sub>S W)) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S ((A \<^sub>S) ,\<^sub>S Y)) \<Longrightarrow> l \<turnstile>d ((X ,\<^sub>S Z) \<turnstile>\<^sub>S (((A \<and>\<^sub>F B) \<^sub>S) ,\<^sub>S (Y ,\<^sub>S W)))"|
Or_R_2: "l \<turnstile>d (Z \<turnstile>\<^sub>S ((B \<^sub>S) ,\<^sub>S X)) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S (((A \<or>\<^sub>F B) \<^sub>S) ,\<^sub>S X))"|
Or_R_1: "l \<turnstile>d (Z \<turnstile>\<^sub>S ((A \<^sub>S) ,\<^sub>S X)) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S (((A \<or>\<^sub>F B) \<^sub>S) ,\<^sub>S X))"
| 
W_L: "l \<turnstile>d (X \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d ((X ,\<^sub>S (A \<^sub>S)) \<turnstile>\<^sub>S Y)"|
P_L: "l \<turnstile>d (((X1 ,\<^sub>S A) ,\<^sub>S (B ,\<^sub>S X2)) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (((X1 ,\<^sub>S B) ,\<^sub>S (A ,\<^sub>S X2)) \<turnstile>\<^sub>S Y)"|
I_R_R2: "l \<turnstile>d (X \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (Y ,\<^sub>S I))"|
A_R2: "l \<turnstile>d (W \<turnstile>\<^sub>S (X ,\<^sub>S (Y ,\<^sub>S Z))) \<Longrightarrow> l \<turnstile>d (W \<turnstile>\<^sub>S ((X ,\<^sub>S Y) ,\<^sub>S Z))"|
A_R: "l \<turnstile>d (W \<turnstile>\<^sub>S ((X ,\<^sub>S Y) ,\<^sub>S Z)) \<Longrightarrow> l \<turnstile>d (W \<turnstile>\<^sub>S (X ,\<^sub>S (Y ,\<^sub>S Z)))"|
I_R_L: "l \<turnstile>d (X \<turnstile>\<^sub>S (I ,\<^sub>S Y)) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"|
I_L_L2: "l \<turnstile>d (X \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d ((I ,\<^sub>S X) \<turnstile>\<^sub>S Y)"|
I_L_R: "l \<turnstile>d ((X ,\<^sub>S I) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"|
C_L: "l \<turnstile>d ((X ,\<^sub>S ((A \<^sub>S) ,\<^sub>S (A \<^sub>S))) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d ((X ,\<^sub>S (A \<^sub>S)) \<turnstile>\<^sub>S Y)"|
C_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (((A \<^sub>S) ,\<^sub>S (A \<^sub>S)) ,\<^sub>S Y)) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S ((A \<^sub>S) ,\<^sub>S Y))"|
I_L_L: "l \<turnstile>d ((I ,\<^sub>S X) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"|
I_R_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (Y ,\<^sub>S I)) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"|
I_L_R2: "l \<turnstile>d (X \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d ((X ,\<^sub>S I) \<turnstile>\<^sub>S Y)"|
A_L: "l \<turnstile>d (((X ,\<^sub>S Y) ,\<^sub>S Z) \<turnstile>\<^sub>S W) \<Longrightarrow> l \<turnstile>d ((X ,\<^sub>S (Y ,\<^sub>S Z)) \<turnstile>\<^sub>S W)"|
P_R: "l \<turnstile>d (X \<turnstile>\<^sub>S ((Y1 ,\<^sub>S A) ,\<^sub>S (B ,\<^sub>S Y2))) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S ((Y1 ,\<^sub>S B) ,\<^sub>S (A ,\<^sub>S Y2)))"|
I_R_L2: "l \<turnstile>d (X \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (I ,\<^sub>S Y))"|
A_L2: "l \<turnstile>d ((X ,\<^sub>S (Y ,\<^sub>S Z)) \<turnstile>\<^sub>S W) \<Longrightarrow> l \<turnstile>d (((X ,\<^sub>S Y) ,\<^sub>S Z) \<turnstile>\<^sub>S W)"|
W_R: "l \<turnstile>d (X \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S ((A \<^sub>S) ,\<^sub>S Y))"
| 
Prem: "(Premise seq) \<in> set l \<Longrightarrow> (\<lambda>x. seq = x) seq \<Longrightarrow> l \<turnstile>d seq"|
Partial: "(Part struct) \<in> set l \<Longrightarrow> (\<lambda>x. (case x of Sequent lhs rhs => struct = lhs \<or> struct = rhs )) seq \<Longrightarrow> l \<turnstile>d seq"|
Id: "l \<turnstile>d ((f \<^sub>S) \<turnstile>\<^sub>S (f \<^sub>S))"
(*calc_structure_rules_se-END*)

end