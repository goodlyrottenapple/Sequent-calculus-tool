theory SequentCalculusEqSets
imports Main SequentCalculus SequentCalculusSets
begin


fun sequentCalculus_to_sequentCalculusSets :: "sequent \<Rightarrow> sequentSets" (">> _") where
"sequentCalculus_to_sequentCalculusSets (X \<turnstile> Y) = set X \<turnstile> set Y"


lemma P_L'': "loc \<turnstile>D ((X1 ; [A]) ; (B ; X2) \<turnstile> Y) \<Longrightarrow> loc \<turnstile>D ((X1 ; B) ; ([A] ; X2) \<turnstile> Y)"
proof (induct B arbitrary: X1 X2 A)
case Nil 
  thus ?case
  by (simp add: SequentCalculus.concat_def)
next
case (Cons b B) 
  have subst1: "((X1 ; [b]) ; [A]) ; (B ; X2) = (X1 ; [b]) ; ([A] ; (B ; X2))"
  by (simp add: SequentCalculus.concat_def)
  have "loc \<turnstile>D ((X1 ; [b]) ; [A]) ; (B ; X2) \<turnstile> Y"
  apply(subst subst1)
  apply(rule_tac derivable'.P_L)
  using Cons(2) by (simp add: SequentCalculus.concat_def)
  with Cons(1) have "loc \<turnstile>D ((X1 ; [b]) ; B) ; ([A] ; X2) \<turnstile> Y" by simp
  thus ?case by (simp add: SequentCalculus.concat_def)
qed


lemma P_L': "loc \<turnstile>D ((X1 ; A) ; (B ; X2) \<turnstile> Y) \<Longrightarrow> loc \<turnstile>D ((X1 ; B) ; (A ; X2) \<turnstile> Y)"
proof (induct A arbitrary: X1 B X2)
case Nil 
  thus ?case
  by (simp add: SequentCalculus.concat_def)
next
case (Cons a A)
  have "loc \<turnstile>D (X1 ; A) ; ([a]; (B ; X2)) \<turnstile> Y"
  apply(rule_tac P_L'')
  using Cons(2) by (simp add: SequentCalculus.concat_def)
  then have "loc \<turnstile>D (X1 ; A) ; (([a];B) ; X2) \<turnstile> Y" by (simp add: SequentCalculus.concat_def)
  with Cons(1) have 1: "loc \<turnstile>D (X1 ; ([a];B)) ; (A ; X2) \<turnstile> Y" by simp
  have subst1: "(X1 ; B) ; ((a # A) ; X2) = (X1 ; B) ; ([a]; (A ; X2))" by (simp add: SequentCalculus.concat_def)
  show ?case
  apply(subst subst1)
  apply(rule_tac P_L'')
  using 1 by (simp add: SequentCalculus.concat_def)
qed

lemma P_R'': "loc \<turnstile>D (Y \<turnstile> (X1 ; [A]) ; (B ; X2)) \<Longrightarrow> loc \<turnstile>D (Y \<turnstile> (X1 ; B) ; ([A] ; X2))"
proof (induct B arbitrary: X1 X2 A)
case Nil 
  thus ?case
  by (simp add: SequentCalculus.concat_def)
next
case (Cons b B) 
  have subst1: "((X1 ; [b]) ; [A]) ; (B ; X2) = (X1 ; [b]) ; ([A] ; (B ; X2))"
  by (simp add: SequentCalculus.concat_def)
  have "loc \<turnstile>D Y \<turnstile> ((X1 ; [b]) ; [A]) ; (B ; X2)"
  apply(subst subst1)
  apply(rule_tac derivable'.P_R)
  using Cons(2) by (simp add: SequentCalculus.concat_def)
  with Cons(1) have "loc \<turnstile>D Y  \<turnstile> ((X1 ; [b]) ; B) ; ([A] ; X2)" by simp
  thus ?case by (simp add: SequentCalculus.concat_def)
qed

lemma P_R': "loc \<turnstile>D (Y \<turnstile> (X1 ; A) ; (B ; X2)) \<Longrightarrow> loc \<turnstile>D (Y \<turnstile> (X1 ; B) ; (A ; X2))"
proof (induct A arbitrary: X1 B X2)
case Nil 
  thus ?case
  by (simp add: SequentCalculus.concat_def)
next
case (Cons a A)
  have "loc \<turnstile>D Y \<turnstile> (X1 ; A) ; ([a]; (B ; X2))"
  apply(rule_tac P_R'')
  using Cons(2) by (simp add: SequentCalculus.concat_def)
  then have "loc \<turnstile>D Y \<turnstile> (X1 ; A) ; (([a];B) ; X2)" by (simp add: SequentCalculus.concat_def)
  with Cons(1) have 1: "loc \<turnstile>D Y \<turnstile> (X1 ; ([a];B)) ; (A ; X2)" by simp
  have subst1: "(X1 ; B) ; ((a # A) ; X2) = (X1 ; B) ; ([a]; (A ; X2))" by (simp add: SequentCalculus.concat_def)
  show ?case
  apply(subst subst1)
  apply(rule_tac P_R'')
  using 1 by (simp add: SequentCalculus.concat_def)
qed

lemma sequentCalculus_to_sequentCalculusSets_subst1: "set (X ; [Y]) = (set X) ;; Y" by (simp add: SequentCalculus.concat_def un_def)
lemma sequentCalculus_to_sequentCalculusSets_subst2: "set ([X] ; Y) = (set Y) ;; X" by (simp add: SequentCalculus.concat_def un_def)



lemma Ds_Sub_L_der:
  assumes "loc \<turnstile>DS X \<turnstile> Y"
  and "X \<subseteq> X'"
  shows "loc \<turnstile>DS X' \<turnstile> Y"

using assms proof (induction "X \<turnstile> Y" arbitrary:X X' Y)

case (Not_L loc X Y A)
  from Not_L(3) obtain X'' where X''_def: "X' = X'' ;; (\<not>\<^sub>F A)" "X \<subseteq> X''" using un_def by auto
  with Not_L have "loc \<turnstile>DS X'' \<turnstile> Y ;; A" by simp
  thus ?case
  apply(subst X''_def)
  apply(rule_tac derivable.Not_L)
  by simp
next
case (And_L loc X A B Z)
  from And_L(3) obtain X'' where X''_def: "X' = X'' ;; (A \<and>\<^sub>F B)" "X \<subseteq> X''" using un_def by auto
  with And_L have "loc \<turnstile>DS (X'' ;; A) ;; B \<turnstile> Z" by (metis insert_mono un_def)
  
  thus ?case
  apply(subst X''_def)
  apply(rule_tac derivable.And_L)
  by simp
next
case (ImpR_R loc Z A X B)
  then have "loc \<turnstile>DS X' ;; A \<turnstile> X ;; B" using un_def by auto
  thus ?case
  apply(rule_tac derivable.ImpR_R)
  by simp
next
case (Or_L loc Z B W X A Y)
  from Or_L(5) obtain X'' where X''_def: "X' = X'' ;; (A \<or>\<^sub>F B)" "X \<subseteq> X''" using un_def by auto
  with Or_L have "loc \<turnstile>DS X'' ;; A \<turnstile> Y" by (metis insert_mono un_def)
  thus ?case
  apply(subst X''_def)
  apply(rule_tac derivable.Or_L)
  using Or_L(1) by simp+
next
case (Not_R loc X A Y)
  show ?case
  apply(rule_tac derivable.Not_R) 
  using Not_R by (metis insert_mono un_def)
next
case (ImpR_L loc X B Y A)
  from ImpR_L(5) obtain X'' where X''_def: "X' = X'' ;; (A \<rightarrow>\<^sub>F B)" "X \<subseteq> X''" using un_def by auto
  with ImpR_L have "loc \<turnstile>DS X'' ;; B \<turnstile> Y" "loc \<turnstile>DS X'' \<turnstile> Y ;; A" by (metis insert_mono un_def)+
  thus ?case
  apply(subst X''_def)
  apply(rule_tac derivable.ImpR_L)
  by simp+
next
case (And_R loc X Y B A)
  show ?case
  apply(rule_tac derivable.And_R)
  using And_R by simp+
next
case (Or_R loc Z X A B)
  show ?case
  apply(rule_tac derivable.Or_R)
  using Or_R by simp+
next
case (Id Y X)
  show ?case
  apply(rule_tac derivable.Id)
  using Id by auto
next
case (Cut f loc X Y)
  show ?case
  apply(rule_tac derivable.Cut)
  using Cut apply simp
  using Cut.hyps(3) Cut.prems un_def apply auto[1]
  by (simp add: Cut.hyps(5) Cut.prems)
qed


lemma Ds_Sub_R_der:
  assumes "loc \<turnstile>DS X \<turnstile> Y"
  and "Y \<subseteq> Y'"
  shows "loc \<turnstile>DS X \<turnstile> Y'"
using assms proof (induction "X \<turnstile> Y" arbitrary:X Y' Y)
case (Not_L loc X Y A)
  show ?case
  apply(rule_tac derivable.Not_L)
  using Not_L using un_def by auto
next
case (And_L loc X A B Z)
  show ?case
  apply(rule_tac derivable.And_L)
  using And_L using un_def by auto
next
case (ImpR_R loc Z A X B)
  from ImpR_R(3) obtain Y'' where Y''_def: "Y' = Y'' ;; (A \<rightarrow>\<^sub>F B)" "X \<subseteq> Y''" using un_def by auto
  with ImpR_R have "loc \<turnstile>DS Z ;; A \<turnstile> Y'' ;; B" by (metis insert_mono un_def)
  thus ?case
  apply(subst Y''_def)
  apply(rule_tac derivable.ImpR_R)
  by simp
next
case (Or_L loc Z B W X A Y)
  show ?case
  apply(rule_tac derivable.Or_L)
  using Or_L by auto
next
case (Not_R loc X A Y)
  from Not_R(3) obtain Y'' where Y''_def: "Y' = Y'' ;; (\<not>\<^sub>F A)" "Y \<subseteq> Y''" using un_def by auto
  with Not_R have "loc \<turnstile>DS X ;; A \<turnstile> Y''" by simp
  thus ?case
  apply(subst Y''_def)
  apply(rule_tac derivable.Not_R)
  by simp
next
case (ImpR_L loc X B Y A)
  show ?case
  apply(rule_tac derivable.ImpR_L)
  using ImpR_L by (metis insert_mono un_def)+
next
case (And_R loc X Y B A)
  from And_R(5) obtain Y'' where Y''_def: "Y' = Y'' ;; (A \<and>\<^sub>F B)" "Y \<subseteq> Y''" using un_def by auto
  with And_R have "loc \<turnstile>DS X \<turnstile> Y'' ;; A" "loc \<turnstile>DS X \<turnstile> Y'' ;; B" by (metis insert_mono un_def)+

  thus ?case
  apply(subst Y''_def)
  apply(rule_tac derivable.And_R)
  using And_R by simp+
next
case (Or_R loc Z X A B)
  from Or_R(3) obtain Y'' where Y''_def: "Y' = Y'' ;; (A \<or>\<^sub>F B)" "X \<subseteq> Y''" using un_def by auto
  with Or_R have "loc \<turnstile>DS Z \<turnstile> (Y'' ;; A) ;; B" by (metis insert_mono un_def)+

  thus ?case
  apply(subst Y''_def)
  apply(rule_tac derivable.Or_R)
  using Or_R by simp+
next
case (Id Y X)
  show ?case
  apply(rule_tac derivable.Id)
  using Id by auto
next
case (Cut f loc X Y)
  show ?case
  apply(rule_tac derivable.Cut)
  using Cut apply simp
  using Cut.hyps(3) Cut.prems un_def apply auto[1]
  using Cut.hyps(5) Cut.prems un_def by auto
qed

lemma sequentCalculus_to_sequentCalculusSets_derivable:
fixes loc
assumes "loc \<turnstile>D seq"
  shows "loc \<turnstile>DS (>> seq)"
using assms apply (induct loc seq)
unfolding sequentCalculus_to_sequentCalculusSets.simps
apply(auto intro:derivable.intros)

apply(subst sequentCalculus_to_sequentCalculusSets_subst1)
apply (rule_tac derivable.Not_L) 
apply (simp add: SequentCalculus.concat_def un_def)

apply(subst sequentCalculus_to_sequentCalculusSets_subst1)
apply(rule_tac derivable.And_L)
apply(rule_tac X="set X ;; A" in Ds_Sub_L_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: subsetI un_def)

apply(subst sequentCalculus_to_sequentCalculusSets_subst1)
apply(rule_tac derivable.And_L)
apply(rule_tac X="set X ;; B" in Ds_Sub_L_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: subsetI un_def)

apply(subst sequentCalculus_to_sequentCalculusSets_subst2)
apply(rule_tac derivable.ImpR_R)
apply (simp add: SequentCalculus.concat_def un_def)

apply(subst sequentCalculus_to_sequentCalculusSets_subst1)
apply(rule_tac derivable.Or_L)
apply (simp add: SequentCalculus.concat_def un_def)
apply(rule_tac X="set X ;; A" in Ds_Sub_L_der)
apply(rule_tac Y="set Y" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(subst sequentCalculus_to_sequentCalculusSets_subst2)
apply(rule_tac derivable.Not_R)
apply (simp add: SequentCalculus.concat_def un_def)

apply(subst sequentCalculus_to_sequentCalculusSets_subst1)
apply(rule_tac derivable.ImpR_L)
apply(rule_tac X="set (Z ; [B])" in Ds_Sub_L_der)
apply(rule_tac Y="set W" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)
apply(rule_tac X="set X" in Ds_Sub_L_der)
apply(rule_tac Y="set ([A] ; Y)" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(subst sequentCalculus_to_sequentCalculusSets_subst2)
apply(rule_tac derivable.And_R)
apply(rule_tac X="set Z" in Ds_Sub_L_der)
apply(rule_tac Y="set([B]; W)" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)
apply(rule_tac X="set X" in Ds_Sub_L_der)
apply(rule_tac Y="set ([A] ; Y)" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(subst sequentCalculus_to_sequentCalculusSets_subst2)
apply(rule_tac derivable.Or_R)
apply(rule_tac Y="set([B]; X)" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(subst sequentCalculus_to_sequentCalculusSets_subst2)
apply(rule_tac derivable.Or_R)
apply(rule_tac Y="set([A]; X)" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(rule_tac X="set X" in Ds_Sub_L_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(rule_tac X="set ((X1 ; [A]) ; ([B] ; X2))" in Ds_Sub_L_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(rule_tac X="set ((X ; [A]) ; [A])" in Ds_Sub_L_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(rule_tac Y="set (([A] ; [A]) ; Y)" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(rule_tac Y="set ((Y1 ; [A]) ; ([B] ; Y2))" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(rule_tac Y="set Y" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(rule_tac derivable.Cut)
apply simp
apply(rule_tac X="set ([f] ; W)" in Ds_Sub_L_der)
apply(rule_tac Y="set Y" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)

apply(rule_tac X="set X" in Ds_Sub_L_der)
apply(rule_tac Y="set (Z ; [f])" in Ds_Sub_R_der)
apply (simp add: SequentCalculus.concat_def un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)
apply (simp add: SequentCalculus.concat_def subsetI un_def)
done

end