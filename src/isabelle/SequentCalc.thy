theory (*calc_name-BEGIN*)SequentCalc(*calc_name-END*)
imports Main (*calc_name_core-BEGIN*)SequentCalc_Core(*calc_name_core-END*) "~~/src/HOL/Library/Multiset" "~~/src/HOL/Library/Code_Char" "~~/src/HOL/Code_Numeral" (*always keep Code_char import last! its added for code generator to output Haskell strings instead of the isabelle nibble stuff *)
begin

(*calc_structure_rules-BEGIN*)
datatype RuleCut = SingleCut

datatype RuleL = And_L_1
               | And_L_2
               | And_R
               | ImpR_L
               | ImpR_R
               | Not_L
               | Not_R
               | Or_L
               | Or_R_1
               | Or_R_2

datatype RuleStruct = A_L
                    | A_L2
                    | A_R
                    | A_R2
                    | C_L
                    | C_R
                    | I_L_L
                    | I_L_L2
                    | I_L_R
                    | I_L_R2
                    | I_R_L
                    | I_R_L2
                    | I_R_R
                    | I_R_R2
                    | P_L
                    | P_R
                    | W_L
                    | W_R

datatype RuleZer = Id
                 | Partial
                 | Prem

datatype Rule = RuleCut RuleCut
              | RuleL RuleL
              | RuleStruct RuleStruct
              | RuleZer RuleZer
              | RuleMacro string Prooftree
              | Fail
     and Prooftree = Prooftree Sequent Rule "Prooftree list" ("_ \<Longleftarrow> PT ( _ ) _" [341,341] 350)
(*calc_structure_rules-END*)

fun concl :: "Prooftree \<Rightarrow> Sequent" where
"concl (a \<Longleftarrow> PT ( b ) c) = a"

datatype ruleder = ruleder      Sequent "Sequent \<Rightarrow> Sequent list option" (infix "\<Longrightarrow>RD" 300) |
                   ruleder_cond "Sequent \<Rightarrow> bool" Sequent "Sequent \<Rightarrow> Sequent list option" ("_ \<Longrightarrow>C _ \<Longrightarrow>RD _" 300)


(*(*uncommentL?Atprop?Formula?Formula_Atprop?Formula_Action_Formula*)
fun is_act_mod :: "Structure \<Rightarrow> Atprop option" where
"is_act_mod (Structure_Formula (Formula_Atprop p)) = Some p"|
"is_act_mod (Structure_Action_Structure _ _ s) = is_act_mod s"|
"is_act_mod _ = None"

fun atom :: "Sequent \<Rightarrow> bool" where
"atom (l \<turnstile>\<^sub>S r) = ( (is_act_mod l) \<noteq> None \<and> (is_act_mod l) = (is_act_mod r) )"|
"atom _ = False"
(*uncommentR?Atprop?Formula?Formula_Atprop?Formula_Action_Formula*)*)

(*(*uncommentL?Action?Action_Freevar?Agent?Agent_Freevar?Formula_Action?Formula_Agent?Sequent_Structure?Sequent*)
fun relAKACheck :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> ((Sequent \<times> Sequent) list) \<Rightarrow> bool" where
"relAKACheck fun mlist = (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure (Formula_Action (?\<^sub>Act ''alpha'') \<^sub>S) ) mlist of 
                   Some (_, Sequent_Structure (Formula_Action alpha \<^sub>S)) \<Rightarrow> 
                      (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure(Structure_Formula(Formula_Agent(Agent_Freevar ''a''))) ) mlist of 
                         Some (_, Sequent_Structure (Formula_Agent a \<^sub>S)) \<Rightarrow> 
                            (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure (Formula_Action (?\<^sub>Act ''beta'') \<^sub>S) ) mlist of 
                                Some (_, Sequent_Structure (Formula_Action beta \<^sub>S)) \<Rightarrow> (case List.find ( \<lambda>(x::Action). x = beta ) (fun alpha a) of Some res \<Rightarrow> True | None \<Rightarrow> False)
                              |  _ \<Rightarrow> False )
                       | _ \<Rightarrow> False)
                 | _ \<Rightarrow> False)"

fun betaList :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> ((Sequent \<times> Sequent) list) \<Rightarrow> (Action list)" where
"betaList fun mlist = (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure (Formula_Action (?\<^sub>Act ''alpha'') \<^sub>S) ) mlist of 
                   Some (_, Sequent_Structure (Formula_Action alpha \<^sub>S)) \<Rightarrow> 
                      (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure(Structure_Formula(Formula_Agent(Agent_Freevar ''a''))) ) mlist of 
                         Some (_, Sequent_Structure (Formula_Agent a \<^sub>S)) \<Rightarrow> fun alpha a
                       | _ \<Rightarrow> [])
                 | _ \<Rightarrow> [])"

fun swapin :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> bool" where
"swapin fun m s = relAKACheck fun (match m s)"
(*uncommentR?Action?Action_Freevar?Agent?Agent_Freevar?Formula_Action?Formula_Agent?Sequent_Structure?Sequent*)*)

(*(*uncommentL?Structure_Bigcomma*)
fun bigcomma_cons_L :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_L ( (B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)) \<turnstile>\<^sub>S Y ) = Some [(;;\<^sub>S (X#Xs) \<turnstile>\<^sub>S Y)]"|
"bigcomma_cons_L _ = None"

fun bigcomma_cons_L2 :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_L2 ( ;;\<^sub>S (X#Xs) \<turnstile>\<^sub>S Y ) = Some [((B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)) \<turnstile>\<^sub>S Y)]"|
"bigcomma_cons_L2 _ = None"


fun bigcomma_cons_R :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_R ( Y \<turnstile>\<^sub>S (B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)) ) = Some [(Y \<turnstile>\<^sub>S ;;\<^sub>S (X#Xs))]"|
"bigcomma_cons_R _ = None"

fun bigcomma_cons_R2 :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_R2 ( Y \<turnstile>\<^sub>S ;;\<^sub>S (X#Xs) ) = Some [(Y \<turnstile>\<^sub>S (B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)))]"|
"bigcomma_cons_R2 _ = None"
(*uncommentR?Structure_Bigcomma*)*)

(*
value"replaceAll (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#(match (ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''alpha'') AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) X))) (AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))"
value"(AgS\<^sub>S (forwK\<^sub>S) (Agent ''a'') (ActS\<^sub>S (forwA\<^sub>S) (Action ''beta'') (((Atprop ''X'') \<^sub>F) \<^sub>S)))"
value"match (ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''alpha'') (AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') (?\<^sub>S ''X''))) (ActS\<^sub>S (forwA\<^sub>S) (Action ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''a'') (((Atprop ''X'') \<^sub>F) \<^sub>S)))"
value"(ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''alpha'') (AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))"
*)

(*(*uncommentL?RuleSwapout*)
fun swapout_L_aux :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> (Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_L_aux relAKA [] seq ( X \<turnstile>\<^sub>S ;;\<^sub>S [] ) = Some []" |
"swapout_L_aux relAKA (b#list) seq ( X \<turnstile>\<^sub>S ;;\<^sub>S ((Y::Structure) # Ys) ) = (
  case ( swapout_L_aux relAKA list seq ( X \<turnstile>\<^sub>S ;;\<^sub>S Ys ) ) of (Some list) \<Rightarrow> 
    (case (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#((?\<^sub>S ''Y''), Y)# (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X)))) of mlist \<Rightarrow>
      (case (replaceAll mlist seq) of applied \<Rightarrow>
        (if (relAKACheck relAKA (List.union (match seq applied) mlist) ) then 
        Some (applied#list) else None)))
| None \<Rightarrow> None)"|
"swapout_L_aux relAKA _ _ _ = None"

fun swapout_L :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_L relAKA seq ( X \<turnstile>\<^sub>S ;;\<^sub>S ((Y::Structure) # Ys) ) = 
    swapout_L_aux relAKA (betaList relAKA (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X))) seq ( X \<turnstile>\<^sub>S ;;\<^sub>S ((Y::Structure) # Ys) ) " |
"swapout_L _ _ _ = None"

fun swapout_L' :: "Action list \<Rightarrow> Action \<Rightarrow> Agent \<Rightarrow> Structure \<Rightarrow> Structure list \<Rightarrow> Sequent list option" where
"swapout_L' [] alpha a X [] = Some ([])" |
"swapout_L' (beta#actionList) alpha a X [] = None" |
"swapout_L' [] alpha a X (Y # Ys) = None" |
"swapout_L' (beta#actionList) alpha a X (Y # Ys) = (case swapout_L' actionList alpha a X Ys of 
   Some list \<Rightarrow> Some ((AgS\<^sub>S forwK\<^sub>S a ActS\<^sub>S forwA\<^sub>S beta X \<turnstile>\<^sub>S Y) #list) | None \<Rightarrow> None )"

fun swapout_L'' :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_L'' relAKA ( ActS\<^sub>S forwA\<^sub>S alpha (AgS\<^sub>S forwK\<^sub>S a X ) \<turnstile>\<^sub>S ;;\<^sub>S list ) = swapout_L' (relAKA alpha a) alpha a X list" |
"swapout_L'' _ _ = None"


fun swapout_R_aux :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> (Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_R_aux relAKA [] seq ( ;;\<^sub>S [] \<turnstile>\<^sub>S X ) = Some []" |
"swapout_R_aux relAKA (b#list) seq ( ;;\<^sub>S ((Y::Structure) # Ys) \<turnstile>\<^sub>S X ) = (
  case ( swapout_R_aux relAKA list seq ( ;;\<^sub>S Ys \<turnstile>\<^sub>S X ) ) of (Some list) \<Rightarrow> 
    (case (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#((?\<^sub>S ''Y''), Y)# (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X)))) of mlist \<Rightarrow>
      (case (replaceAll mlist seq) of applied \<Rightarrow>
        (if (relAKACheck relAKA (List.union (match seq applied) mlist) ) then 
        Some (applied#list) else None)))
| None \<Rightarrow> None)"|
"swapout_R_aux _ _ _ _ = None"


fun swapout_R :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_R relAKA seq ( ;;\<^sub>S ((Y::Structure) # Ys) \<turnstile>\<^sub>S X ) = 
    swapout_R_aux relAKA (betaList relAKA (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X))) seq ( ;;\<^sub>S ((Y::Structure) # Ys) \<turnstile>\<^sub>S X ) " |
"swapout_R _ _ _ = None"
(*uncommentR?RuleSwapout*)*)


(*(*uncommentL?Pre_L*)
fun pre_l :: "Action \<Rightarrow> Sequent \<Rightarrow> bool" where
"pre_l a ((One\<^sub>F alpha)\<^sub>S \<turnstile>\<^sub>S X) = (a = alpha)"|
"pre_l a _ = False"
(*uncommentR?Pre_L*)*)

(*(*uncommentL?Pre_R*)
fun pre_r :: "Action \<Rightarrow> Sequent \<Rightarrow> bool" where
"pre_r a (X \<turnstile>\<^sub>S (One\<^sub>F alpha)\<^sub>S) = (a = alpha)"|
"pre_r a _ = False"
(*uncommentR?Pre_R*)*)

(*
fun relAKAA :: "Action \<Rightarrow> Agent \<Rightarrow> Action \<Rightarrow> bool" where
"relAKAA (Action x) (Agent a) (Action y) = ((x = y) \<or> (x=''ep'' \<and> a = ''c'' \<and> y=''ew''))" |
"relAKAA _ _ _ = False"

definition "const_seq = ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))"
definition "seq_empty = ((;;\<^sub>S []) \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (Action ''epa'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''c'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S))))"
definition "seq = ((;;\<^sub>S [((AgF\<^sub>F (fboxK\<^sub>F) (Agent ''c'') (B\<^sub>F (Pre\<^sub>F (Action ''epa'')) (\<rightarrow>\<^sub>F) ((Atprop ''Ga'') \<^sub>F))) \<^sub>S)]) \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (Action ''epa'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''c'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S))))"
definition "seqO = (((AgF\<^sub>F (fboxK\<^sub>F) (Agent ''c'') (B\<^sub>F (Pre\<^sub>F (Action ''epa'')) (\<rightarrow>\<^sub>F) ((Atprop ''Ga'') \<^sub>F))) \<^sub>S) \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (Agent ''c'') ActS\<^sub>S forwA\<^sub>S (Action ''epa'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S) )"

definition "mtchList X b Y= (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#((?\<^sub>S ''Y''), Y)# (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X))))"

definition "mList = mtchList ((ActS\<^sub>S (forwA\<^sub>S) (Action ''epa'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''c'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S)))) (Action(''epa'')) ((AgF\<^sub>F (fboxK\<^sub>F) (Agent ''c'') (B\<^sub>F (Pre\<^sub>F (Action ''epa'')) (\<rightarrow>\<^sub>F) ((Atprop ''Ga'') \<^sub>F))) \<^sub>S)"
value " match (((?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))) seqO "
value "relAKACheck relAKAA (List.union (match (((?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))) seqO) mList)"
value "swapout_R relAKAA [] const_seq seq_empty"
value "swapout_R relAKAA [Action(''epa'')] const_seq seq"


value"swapout_L rel blist ( (?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X'') )"
*)


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

(*rules_rule_fun-BEGIN*)
primrec ruleRuleCut :: "Locale \<Rightarrow> RuleCut \<Rightarrow> ruleder" where
"ruleRuleCut x RuleCut.SingleCut = ( case x of (CutFormula f) \<Rightarrow>((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (?\<^sub>S ''W'')) \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Z'') (,\<^sub>S) (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S B\<^sub>S (?\<^sub>S ''Z'') ,\<^sub>S (f \<^sub>S)),( B\<^sub>S (f \<^sub>S) ,\<^sub>S (?\<^sub>S ''W'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))]) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )"

primrec ruleRuleL :: "Locale \<Rightarrow> RuleL \<Rightarrow> ruleder" where
"ruleRuleL x RuleL.Not_L = ((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) ((U\<^sub>F (\<not>\<^sub>F) (?\<^sub>F ''A'')) \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (,\<^sub>S) (?\<^sub>S ''Y'')))])" |
"ruleRuleL x RuleL.And_L_1 = ((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) ((B\<^sub>F (?\<^sub>F ''A'') (\<and>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Z'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) ((?\<^sub>F ''A'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleL x RuleL.And_L_2 = ((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) ((B\<^sub>F (?\<^sub>F ''A'') (\<and>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Z'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) ((?\<^sub>F ''B'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleL x RuleL.ImpR_R = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S ((B\<^sub>F (?\<^sub>F ''A'') (\<rightarrow>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S) (,\<^sub>S) (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''Z'') (,\<^sub>S) ((?\<^sub>F ''A'') \<^sub>S)) \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''B'') \<^sub>S) (,\<^sub>S) (?\<^sub>S ''X'')))])" |
"ruleRuleL x RuleL.Or_L = ((B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (?\<^sub>S ''Z'')) (,\<^sub>S) ((B\<^sub>F (?\<^sub>F ''A'') (\<or>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S)) \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Y'') (,\<^sub>S) (?\<^sub>S ''W''))) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) ((?\<^sub>F ''A'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')),((B\<^sub>S (?\<^sub>S ''Z'') (,\<^sub>S) ((?\<^sub>F ''B'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''W''))])" |
"ruleRuleL x RuleL.Not_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S ((U\<^sub>F (\<not>\<^sub>F) (?\<^sub>F ''A'')) \<^sub>S) (,\<^sub>S) (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) ((?\<^sub>F ''A'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleL x RuleL.ImpR_L = ((B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (?\<^sub>S ''Z'')) (,\<^sub>S) ((B\<^sub>F (?\<^sub>F ''A'') (\<rightarrow>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S)) \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Y'') (,\<^sub>S) (?\<^sub>S ''W''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (,\<^sub>S) (?\<^sub>S ''Y''))),((B\<^sub>S (?\<^sub>S ''Z'') (,\<^sub>S) ((?\<^sub>F ''B'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''W''))])" |
"ruleRuleL x RuleL.And_R = ((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (?\<^sub>S ''Z'')) \<turnstile>\<^sub>S (B\<^sub>S ((B\<^sub>F (?\<^sub>F ''A'') (\<and>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S) (,\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (,\<^sub>S) (?\<^sub>S ''W'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (,\<^sub>S) (?\<^sub>S ''Y''))),((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''B'') \<^sub>S) (,\<^sub>S) (?\<^sub>S ''W'')))])" |
"ruleRuleL x RuleL.Or_R_2 = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S ((B\<^sub>F (?\<^sub>F ''A'') (\<or>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S) (,\<^sub>S) (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''B'') \<^sub>S) (,\<^sub>S) (?\<^sub>S ''X'')))])" |
"ruleRuleL x RuleL.Or_R_1 = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S ((B\<^sub>F (?\<^sub>F ''A'') (\<or>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S) (,\<^sub>S) (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (,\<^sub>S) (?\<^sub>S ''X'')))])"

primrec ruleRuleStruct :: "Locale \<Rightarrow> RuleStruct \<Rightarrow> ruleder" where
"ruleRuleStruct x RuleStruct.W_L = ((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) ((?\<^sub>F ''A'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.P_L = ((B\<^sub>S (B\<^sub>S (?\<^sub>S ''X1'') (,\<^sub>S) (?\<^sub>S ''B'')) (,\<^sub>S) (B\<^sub>S (?\<^sub>S ''A'') (,\<^sub>S) (?\<^sub>S ''X2''))) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (B\<^sub>S (?\<^sub>S ''X1'') (,\<^sub>S) (?\<^sub>S ''A'')) (,\<^sub>S) (B\<^sub>S (?\<^sub>S ''B'') (,\<^sub>S) (?\<^sub>S ''X2''))) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.I_R_R2 = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Y'') (,\<^sub>S) (Z\<^sub>S (I)))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.A_R2 = ((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (?\<^sub>S ''Y'')) (,\<^sub>S) (?\<^sub>S ''Z''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (,\<^sub>S) (?\<^sub>S ''Z''))))])" |
"ruleRuleStruct x RuleStruct.A_R = ((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (,\<^sub>S) (?\<^sub>S ''Z'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (?\<^sub>S ''Y'')) (,\<^sub>S) (?\<^sub>S ''Z'')))])" |
"ruleRuleStruct x RuleStruct.I_R_L = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (Z\<^sub>S (I)) (,\<^sub>S) (?\<^sub>S ''Y'')))])" |
"ruleRuleStruct x RuleStruct.I_L_L2 = ((B\<^sub>S (Z\<^sub>S (I)) (,\<^sub>S) (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.I_L_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (Z\<^sub>S (I))) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.C_L = ((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) ((?\<^sub>F ''A'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (,\<^sub>S) ((?\<^sub>F ''A'') \<^sub>S))) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.C_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (,\<^sub>S) (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (,\<^sub>S) ((?\<^sub>F ''A'') \<^sub>S)) (,\<^sub>S) (?\<^sub>S ''Y'')))])" |
"ruleRuleStruct x RuleStruct.I_L_L = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (Z\<^sub>S (I)) (,\<^sub>S) (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.I_R_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Y'') (,\<^sub>S) (Z\<^sub>S (I))))])" |
"ruleRuleStruct x RuleStruct.I_L_R2 = ((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (Z\<^sub>S (I))) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.A_L = ((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (,\<^sub>S) (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''W'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (?\<^sub>S ''Y'')) (,\<^sub>S) (?\<^sub>S ''Z'')) \<turnstile>\<^sub>S (?\<^sub>S ''W''))])" |
"ruleRuleStruct x RuleStruct.P_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (B\<^sub>S (?\<^sub>S ''Y1'') (,\<^sub>S) (?\<^sub>S ''B'')) (,\<^sub>S) (B\<^sub>S (?\<^sub>S ''A'') (,\<^sub>S) (?\<^sub>S ''Y2'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (B\<^sub>S (?\<^sub>S ''Y1'') (,\<^sub>S) (?\<^sub>S ''A'')) (,\<^sub>S) (B\<^sub>S (?\<^sub>S ''B'') (,\<^sub>S) (?\<^sub>S ''Y2''))))])" |
"ruleRuleStruct x RuleStruct.I_R_L2 = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (Z\<^sub>S (I)) (,\<^sub>S) (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.A_L2 = ((B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (?\<^sub>S ''Y'')) (,\<^sub>S) (?\<^sub>S ''Z'')) \<turnstile>\<^sub>S (?\<^sub>S ''W'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (,\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (,\<^sub>S) (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''W''))])" |
"ruleRuleStruct x RuleStruct.W_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (,\<^sub>S) (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])"

primrec ruleRuleZer :: "Locale \<Rightarrow> RuleZer \<Rightarrow> ruleder" where
"ruleRuleZer x RuleZer.Prem = ( case x of (Premise seq) \<Rightarrow>(\<lambda>x. seq = x) \<Longrightarrow>C ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some []) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )" |
"ruleRuleZer x RuleZer.Partial = ( case x of (Part struct) \<Rightarrow>(\<lambda>x. (case x of Sequent lhs rhs => struct = lhs \<or> struct = rhs )) \<Longrightarrow>C ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some []) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )" |
"ruleRuleZer x RuleZer.Id = (((?\<^sub>F ''f'') \<^sub>S) \<turnstile>\<^sub>S ((?\<^sub>F ''f'') \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [])"

fun rule :: "Locale \<Rightarrow> Rule \<Rightarrow> ruleder" where
"rule l (RuleCut r) = ruleRuleCut l r" |
"rule l (RuleL r) = ruleRuleL l r" |
"rule l (RuleStruct r) = ruleRuleStruct l r" |
"rule l (RuleZer r) = ruleRuleZer l r" |
"rule _ _ = ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None)"
(*rules_rule_fun-END*)

fun fst :: "ruleder \<Rightarrow> Sequent" and snd :: "ruleder \<Rightarrow> Sequent \<Rightarrow> Sequent list option" and cond :: "ruleder \<Rightarrow> (Sequent \<Rightarrow> bool) option" where
"fst (ruleder x _) = x" |
"fst (ruleder_cond _ x _) = x" |
"snd (ruleder _ y) = y" |
"snd (ruleder_cond _ _ y) = y" |
"cond (ruleder_cond c _ _) = Some c" |
"cond (ruleder _ _) = None"

fun der :: "Locale \<Rightarrow> Rule \<Rightarrow> Sequent \<Rightarrow> (Rule * Sequent list)"
where
"der l r s =( case (snd (rule l r)) s of
                None \<Rightarrow> (Fail, [])
              | Some conclusion \<Rightarrow> 
                  if (ruleMatch (fst (rule l r)) s) then 
                    case cond (rule l r) of 
                      None \<Rightarrow> ( r, map (replaceAll (match (fst (rule l r)) s) ) conclusion )
                    | Some condition \<Rightarrow> ( if condition s 
                        then (r, map (replaceAll (match (fst (rule l r)) s) ) conclusion )
                        else (Fail, []) )
                  else (Fail, []) )"


(*(*uncommentL?RuleCut-BEGIN*)*)(*uncommentL?RuleCut-END*)
(*der cut applies a supplied formula if the cut rule is used - a bit hacky atm *) 
(*fun der_cut :: "Rule \<Rightarrow> Formula \<Rightarrow> Sequent \<Rightarrow> (Rule * Sequent list)"
where
"der_cut (RuleCut RuleCut.SingleCut) cutForm s = (if (ruleMatch (fst (rule (RuleCut RuleCut.SingleCut))) s) 
   then ((RuleCut RuleCut.SingleCut), map (replaceAll (match (fst (rule (RuleCut RuleCut.SingleCut))) s @ (map (\<lambda>(x,y). (Sequent_Structure (Structure_Formula x), Sequent_Structure (Structure_Formula y))) (match (?\<^sub>F''A'') cutForm))) ) (snd (rule (RuleCut RuleCut.SingleCut)))) 
   else (Fail, []))" |
"der_cut _ _ _ = (Fail, [])"*)
(*uncommentR?RuleCut-BEGIN*)(*(*uncommentR?RuleCut-END*)*)

primrec ant :: "Sequent \<Rightarrow> Structure" where
"ant (Sequent x y) = x" |
"ant (Sequent_Structure x) = x"
primrec consq :: "Sequent \<Rightarrow> Structure" where
"consq (Sequent x y) = y"|
"consq (Sequent_Structure x) = x"

fun replaceIntoPT_aux :: "(Sequent \<times> Sequent) list \<Rightarrow> Prooftree \<Rightarrow> Prooftree" and 
  replaceIntoPT_list :: "(Sequent \<times> Sequent) list \<Rightarrow> Prooftree list \<Rightarrow> Prooftree list" where 
"replaceIntoPT_aux list (Prooftree c (RuleMacro s pt) ptlist) = Prooftree (replaceAll list c) (RuleMacro s (replaceIntoPT_aux list pt)) (replaceIntoPT_list list ptlist)" |
"replaceIntoPT_aux list (Prooftree c r ptlist) = Prooftree (replaceAll list c) r (replaceIntoPT_list list ptlist)" |
"replaceIntoPT_list list [] = []" |
"replaceIntoPT_list list (l#ist) = (replaceIntoPT_aux list l)#(replaceIntoPT_list list ist)"

fun replaceIntoPT :: "Sequent \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replaceIntoPT seq (Prooftree c r ptlist) = replaceIntoPT_aux (match c seq) (Prooftree c r ptlist)"


fun collectPremises :: "Prooftree \<Rightarrow> Sequent list" where
"collectPremises (Prooftree p (RuleZer Prem) []) = [p]" |
"collectPremises (Prooftree _ (RuleMacro _ pt) list) = foldr append (map collectPremises list) []" |
"collectPremises (Prooftree _ _ list) = foldr append (map collectPremises list) []"

fun collectPremisesToLocale :: "Prooftree \<Rightarrow> Locale list" where
"collectPremisesToLocale pt = map Premise (collectPremises pt)"

fun collectCutFormulas :: "Prooftree \<Rightarrow> Formula list" where
"collectCutFormulas (Prooftree _ (RuleCut _) [l, r]) = (
  (case (consq (concl l)) of (Structure_Formula f) \<Rightarrow> (case (ant (concl r)) of (Structure_Formula f') \<Rightarrow> (if f = f' then [f] @ (collectCutFormulas l) @ (collectCutFormulas r) else (collectCutFormulas l) @ (collectCutFormulas r)) |  _ \<Rightarrow> (collectCutFormulas l) @ (collectCutFormulas r) ) |
    _ \<Rightarrow> (case (consq (concl r)) of (Structure_Formula f) \<Rightarrow> (case (ant (concl l)) of (Structure_Formula f') \<Rightarrow> (if f = f' then [f] @ (collectCutFormulas l) @ (collectCutFormulas r) else (collectCutFormulas l) @ (collectCutFormulas r)) |  _ \<Rightarrow> (collectCutFormulas l) @ (collectCutFormulas r)))
  )
)" |
"collectCutFormulas (Prooftree _ (RuleMacro _ pt) list) = foldr append (map collectCutFormulas list) (collectCutFormulas pt)" |
"collectCutFormulas (Prooftree _ _ list) = foldr append (map collectCutFormulas list) []"

fun collectCutFormulasToLocale :: "Prooftree \<Rightarrow> Locale list" where
"collectCutFormulasToLocale pt = map CutFormula (collectCutFormulas pt)"


fun isProofTree :: "Locale list \<Rightarrow> Prooftree \<Rightarrow> bool" where
"isProofTree loc (s \<Longleftarrow> PT(RuleMacro n pt) ptlist) = (
  s = (concl pt) \<and> 
  isProofTree (append loc (collectPremisesToLocale pt)) pt \<and>
  set (collectPremises pt) = set (map concl ptlist) \<and>
  foldr (op \<and>) (map (isProofTree loc) ptlist) True
)"|
"isProofTree loc (s \<Longleftarrow> PT(r) l) = ( 
  foldr (op \<and>) (map (isProofTree loc) l) True \<and>
  foldr (op \<or>) (map (\<lambda>x. (
    set (Product_Type.snd (der x r s)) = set (map concl l) \<and> 
    Fail \<noteq> Product_Type.fst (der x r s)
  )) loc) False
)"


fun isProofTreeWoMacro :: "Locale list \<Rightarrow> Prooftree \<Rightarrow> bool" where
"isProofTreeWoMacro loc (s \<Longleftarrow> PT(RuleMacro n pt) ptlist) = False"|
"isProofTreeWoMacro loc (s \<Longleftarrow> PT(r) l) = ( 
  foldr (op \<and>) (map (isProofTreeWoMacro loc) l) True \<and>
  foldr (op \<or>) (map (\<lambda>x. (
    set (Product_Type.snd (der x r s)) = set (map concl l) \<and> 
    Fail \<noteq> Product_Type.fst (der x r s)
  )) loc) False
)"

fun isProofTreeWithCut :: "Locale list \<Rightarrow> Prooftree \<Rightarrow> bool" where
"isProofTreeWithCut loc pt = isProofTree (append loc (collectCutFormulasToLocale pt)) pt"


(*"isProofTree loc (s \<Longleftarrow> B(r) l) = ( foldr (op \<and>) (map (isProofTree loc) l) True \<and> set (Product_Type.snd (der r s)) = set (map concl l) )"*)

(*
fun isProofTreeWCut :: "Prooftree \<Rightarrow> bool" where
"isProofTreeWCut (s \<Longleftarrow> C(f) t1 ; t2) = (isProofTreeWCut t1 \<and> isProofTreeWCut t2 \<and> (case (der_cut (RuleCut RuleCut.SingleCut) f s) of (Fail, []) \<Rightarrow> False | (ru,[se1, se2]) \<Rightarrow> (se1 = concl t1 \<and> se2 = concl t2) \<or> (se1 = concl t2 \<and> se2 = concl t1)))" |
"isProofTreeWCut (s \<Longleftarrow> Z(r)) = ruleMatch (fst (rule (RuleZer r))) s" | 
"isProofTreeWCut (s \<Longleftarrow> U(r) t) = (isProofTreeWCut t \<and> (case (der (RuleU r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> D(r) t) = (isProofTreeWCut t \<and> (case (der (RuleDisp r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> O(r) t) = (isProofTreeWCut t \<and> (case (der (RuleOp r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> B(r) t1 ; t2) = (isProofTreeWCut t1 \<and> isProofTreeWCut t2 \<and> (case (der (RuleBin r) s) of (Fail, []) \<Rightarrow> False | (ru,[se1, se2]) \<Rightarrow> (se1 = concl t1 \<and> se2 = concl t2) \<or> (se1 = concl t2 \<and> se2 = concl t1)))"

lemma isProofTree_concl_freevars[simp]:
  fixes pt
  assumes "isProofTree pt"
  shows "freevars (concl pt) = {}"
proof (cases pt)
case (Zer s r)
  from assms have 1: "ruleMatch (fst (rule (RuleZer r))) s" by (metis (poly_guards_query) Zer isProofTree.simps(1))
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Zer concl.simps)
next
case (Unary s r t)
  with assms  have "(der (RuleU r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleU r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Unary concl.simps)
next
case (Display s r t)
  with assms  have "(der (RuleDisp r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleDisp r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Display concl.simps)
next
case (Operational s r t)
  with assms  have "(der (RuleOp r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleOp r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Operational concl.simps(4))
next
case (Binary s r t1 t2)
  with assms  have "(der (RuleBin r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleBin r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Binary concl.simps)
next
case (Cut s r t1 t2)
  then have False by (metis assms isProofTree.simps)
  thus ?thesis ..
qed
*)
(*
- equality of shallow and deep terms
  - for every deep-term with a valid proof tree there is an equivalent shallow-term in the set derivable
  - shallow\<Rightarrow>deep possible induction proof on the rules of the shallow embedding set*)

definition "ruleList = (*rules_rule_list-BEGIN*)(map (RuleCut) [SingleCut]) @ (map (RuleL) [Not_L,And_L_1,And_L_2,ImpR_R,Or_L,Not_R,ImpR_L,And_R,Or_R_2,Or_R_1]) @ (map (RuleStruct) [W_L,P_L,I_R_R2,A_R2,A_R,I_R_L,I_L_L2,I_L_R,C_L,C_R,I_L_L,I_R_R,I_L_R2,A_L,P_R,I_R_L2,A_L2,W_R]) @ (map (RuleZer) [Prem,Partial,Id])(*rules_rule_list-END*)"

lemma Atprop_without_Freevar[simp]: "\<And>a. freevars a = {} \<Longrightarrow> \<exists>q. a = Atprop q"
  by (metis Atprop.exhaust freevars_Atprop.simps(1) insert_not_empty)

(*
(*perhaps things bellow should be moved to a separate utils file?? *)

fun replaceLPT :: "Prooftree \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replaceLPT (s \<Longleftarrow> B(r) t1 ; t2) rep = (s \<Longleftarrow> B(r) rep ; t2)" |
"replaceLPT pt rep = pt"

fun replaceRPT :: "Prooftree \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replaceRPT (s \<Longleftarrow> B(r) t1 ; t2) rep = (s \<Longleftarrow> B(r) t1 ; rep)" |
"replaceRPT pt rep = pt"
*)

(*(*uncommentL?Agent?Agent_Freevar*)
primrec rulifyAgent :: "Agent \<Rightarrow> Agent" where
"rulifyAgent (Agent a) = Agent_Freevar a" |
"rulifyAgent (Agent_Freevar a) = Agent_Freevar a"
(*uncommentR?Agent?Agent_Freevar*)*)

(*(*uncommentL?Action?Action_Freevar*)
primrec rulifyAction :: "Action \<Rightarrow> Action" where
"rulifyAction (Action a) = Action_Freevar a" |
"rulifyAction (Action_Freevar a) = Action_Freevar a"
(*uncommentR?Action?Action_Freevar*)*)

(*(*uncommentL?Formula-BEGIN*)*)(*uncommentL?Formula-END*)
fun rulifyFormula :: "Formula \<Rightarrow> Formula" where
(*(*uncommentL?Formula_Atprop-BEGIN*)*)(*uncommentL?Formula_Atprop-END*)
"rulifyFormula (Formula_Atprop(Atprop (f#a))) = 
(if CHR ''A'' \<le> f \<and> f \<le> CHR ''Z'' then (Formula_Freevar (f#a)) else (Formula_Atprop (Atprop_Freevar (f#a)))
)" |
(*uncommentR?Formula_Atprop-BEGIN*)(*(*uncommentR?Formula_Atprop-END*)*)
(*(*uncommentL?Formula_Bin-BEGIN*)*)(*uncommentL?Formula_Bin-END*)
"rulifyFormula (Formula_Bin x c y) = (Formula_Bin (rulifyFormula x) c (rulifyFormula y))" |
(*uncommentR?Formula_Bin-BEGIN*)(*(*uncommentR?Formula_Bin-END*)*)
(*(*uncommentL?Formula_Agent_Formula*)
"rulifyFormula (Formula_Agent_Formula c a x) = (Formula_Agent_Formula c (rulifyAgent a) (rulifyFormula x) )" |
(*uncommentR?Formula_Agent_Formula*)*)
(*(*uncommentL?Formula_Action_Formula*)
"rulifyFormula (Formula_Action_Formula c a x) = (Formula_Action_Formula c (rulifyAction a) (rulifyFormula x) )" |
(*uncommentR?Formula_Action_Formula*)*)
(*(*uncommentL?Formula_Precondition*)
"rulifyFormula (Formula_Precondition a) = (Formula_Precondition (rulifyAction a))" |
(*uncommentR?Formula_Precondition*)*)
"rulifyFormula x = x"
(*uncommentR?Formula-BEGIN*)(*(*uncommentR?Formula-END*)*)

(*(*uncommentL?Structure-BEGIN*)*)(*uncommentL?Structure-END*)
fun rulifyStructure :: "Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Formula?Formula_Atprop-BEGIN*)*)(*uncommentL?Structure_Formula?Formula_Atprop-END*)
"rulifyStructure (Structure_Formula (Formula_Atprop(Atprop (f#a)))) = 
(if CHR ''A'' \<le> f \<and> f \<le> CHR ''Z'' then (
  if f = CHR ''F'' then Structure_Formula (Formula_Freevar (f#a)) else Structure_Freevar (f#a)
  ) else Structure_Formula (Formula_Atprop (Atprop_Freevar (f#a)))
)" |
(*uncommentR?Structure_Formula?Formula_Atprop-BEGIN*)(*(*uncommentR?Structure_Formula?Formula_Atprop-END*)*)
(*(*uncommentL?Structure_Formula-BEGIN*)*)(*uncommentL?Structure_Formula-END*)
"rulifyStructure (Structure_Formula x) = Structure_Formula (rulifyFormula x)" | 
(*uncommentR?Structure_Formula-BEGIN*)(*(*uncommentR?Structure_Formula-END*)*)
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*)
"rulifyStructure (Structure_Bin x c y) = (Structure_Bin (rulifyStructure x) c (rulifyStructure y))" |
(*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Agent_Structure*)
"rulifyStructure (Structure_Agent_Structure c a x) = (Structure_Agent_Structure c (rulifyAgent a) (rulifyStructure x) )" |
(*uncommentR?Structure_Agent_Structure*)*)
(*(*uncommentL?Structure_Action_Structure*)
"rulifyStructure (Structure_Action_Structure c a x) = (Structure_Action_Structure c (rulifyAction a) (rulifyStructure x) )" |
(*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Bigcomma*)
"rulifyStructure (Structure_Bigcomma list) = (Structure_Bigcomma (map rulifyStructure list))" |
(*uncommentR?Structure_Bigcomma*)*)
(*(*uncommentL?Structure_Phi*)
"rulifyStructure (Structure_Phi a) = (Structure_Phi (rulifyAction a))" |
(*uncommentR?Structure_Phi*)*)
"rulifyStructure x = x"
(*uncommentR?Structure-BEGIN*)(*(*uncommentR?Structure-END*)*)

(*(*uncommentL?Sequent-BEGIN*)*)(*uncommentL?Sequent-END*)
primrec rulifySequent :: "Sequent \<Rightarrow> Sequent" where
"rulifySequent (Sequent x y) = Sequent (rulifyStructure x) (rulifyStructure y)"|
"rulifySequent (Sequent_Structure x) = (Sequent_Structure x)"
(*uncommentR?Sequent-BEGIN*)(*(*uncommentR?Sequent-END*)*)

fun rulifyProoftree :: "Prooftree \<Rightarrow> Prooftree" where
"rulifyProoftree (Prooftree s (RuleMacro str pt) list) = Prooftree (rulifySequent s) (RuleMacro str (rulifyProoftree pt)) (map rulifyProoftree list)" |
"rulifyProoftree (Prooftree s r list) = (Prooftree (rulifySequent s) r (map rulifyProoftree list))"


fun replaceIntoProoftree :: "Prooftree list \<Rightarrow> Prooftree \<Rightarrow> Prooftree"  where
"replaceIntoProoftree [] (Prooftree s (RuleZer Prem) []) = (Prooftree s (RuleZer Prem) [])" |
"replaceIntoProoftree (l#ist) (Prooftree s (RuleZer Prem) []) = (if (concl l) = s then l else replaceIntoProoftree ist (Prooftree s (RuleZer Prem) []))" |
"replaceIntoProoftree list (Prooftree s r []) =  (Prooftree s r [])" |
"replaceIntoProoftree list (Prooftree s r l) =  (Prooftree s r (map (replaceIntoProoftree list) l))"

fun expandProoftree :: "Prooftree \<Rightarrow> Prooftree"  where
"expandProoftree (Prooftree _ (RuleMacro n (Prooftree s r l)) list) = (Prooftree s r (map (replaceIntoProoftree (map expandProoftree list)) (map expandProoftree l)))" |
"expandProoftree (Prooftree s r list) = Prooftree s r (map expandProoftree list)"

fun collect_freevars_Structure :: "Structure \<Rightarrow> Structure list" where
(*(*uncommentL?Structure_Formula-BEGIN*)*)(*uncommentL?Structure_Formula-END*)  "collect_freevars_Structure (Structure_Formula f) = [Structure_Formula f]" (*uncommentR?Structure_Formula-BEGIN*)(*(*uncommentR?Structure_Formula-END*)*)
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) | "collect_freevars_Structure (Structure_Bin l _ r) = (collect_freevars_Structure l) @ (collect_freevars_Structure r)" (*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Freevar-BEGIN*)*)(*uncommentL?Structure_Freevar-END*) | "collect_freevars_Structure (Structure_Freevar free) = [Structure_Freevar free]" (*uncommentR?Structure_Freevar-BEGIN*)(*(*uncommentR?Structure_Freevar-END*)*)
(*(*uncommentL?Structure_Action_Structure*) | "collect_freevars_Structure (Structure_Action_Structure oper ac struct) = [Structure_Formula (Formula_Action ac)] @ (collect_freevars_Structure struct)" (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) | "collect_freevars_Structure (Structure_Agent_Structure oper ag struct) = [Structure_Formula (Formula_Agent ag)] @ (collect_freevars_Structure struct)" (*uncommentR?Structure_Agent_Structure*)*)
(*(*uncommentL?Structure_Phi*) | "collect_freevars_Structure (Structure_Phi a) = [Structure_Phi a]"  (*uncommentR?Structure_Phi*)*)
(*(*uncommentL?Structure_Zer-BEGIN*)*)(*uncommentL?Structure_Zer-END*) | "collect_freevars_Structure (Structure_Zer z) = [Structure_Zer z]" (*uncommentR?Structure_Zer-BEGIN*)(*(*uncommentR?Structure_Zer-END*)*)
(*(*uncommentL?Structure_Bigcomma*) | "collect_freevars_Structure (Structure_Bigcomma list) = foldr (op @) (map collect_freevars_Structure list) []" (*uncommentR?Structure_Bigcomma*)*)


fun collect_freevars_Sequent :: "Sequent \<Rightarrow> Structure list" where
"collect_freevars_Sequent (Sequent l r) = (collect_freevars_Structure l) @ (collect_freevars_Structure r)" |
"collect_freevars_Sequent (Sequent_Structure _) = []"


fun is_display_rule :: "Rule \<Rightarrow> Rule list" where
"is_display_rule r = 
(if (case (snd (rule Empty r) (fst (rule Empty r)) ) of Some list \<Rightarrow>
  (case list of h#rest \<Rightarrow>
  multiset_of (collect_freevars_Sequent (fst (rule Empty r))) = 
  multiset_of (collect_freevars_Sequent h ) | _ \<Rightarrow> False ) | _ \<Rightarrow> False )
then [r] 
else [])"

definition displayRules :: "Rule list" where
"displayRules = foldr (op @) (map is_display_rule ruleList) []"

value "displayRules"

(*
definition "lhs = collect_freevars_Sequent (fst (rule Empty (RuleStruct I_impL)))"
definition "rhs = collect_freevars_Sequent (hd (the (snd (rule Empty (RuleStruct I_impL)) (fst (rule Empty (RuleStruct E_L)))  )))"

value "multiset_of lhs = multiset_of rhs"
*)

datatype polarity = Plus ("+p") | Minus ("-p") | N

fun polarity_weird_xor :: "polarity \<Rightarrow> polarity \<Rightarrow> polarity" (infix "\<or>p" 400) where
"polarity_weird_xor +p N = +p" |
"polarity_weird_xor -p N = -p" |
"polarity_weird_xor N x = x" |
"polarity_weird_xor +p _ = N" |
"polarity_weird_xor -p _ = N"


fun polarity_not :: "polarity \<Rightarrow> polarity" ( "\<not>p _") where
"polarity_not -p = +p" |
"polarity_not +p = -p" |
"polarity_not N = N"


fun polarity_weird_and :: "polarity \<Rightarrow> polarity \<Rightarrow> polarity" (infix "\<and>p" 400) where
"polarity_weird_and -p x = \<not>p x" |
"polarity_weird_and +p x = x" |
"polarity_weird_and N _ = N"

lemma polarity_weird_xor_comm: "a \<or>p b = b \<or>p a"
apply (cases a, (cases b, auto)+)
done

lemma polarity_weird_and_comm: "a \<and>p b = b \<and>p a"
apply (cases a, (cases b, auto)+)
done

fun structure_Op_polarity :: "Structure_Bin_Op \<Rightarrow> (polarity \<times> polarity)" where
(*(*uncommentL?Structure_Comma-BEGIN*)*)(*uncommentL?Structure_Comma-END*) 
   "structure_Op_polarity Structure_Comma = (+p, +p)"
(*uncommentR?Structure_Comma-BEGIN*)(*(*uncommentR?Structure_Comma-END*)*)
(*(*uncommentL?Structure_ImpL*) 
 | "structure_Op_polarity Structure_ImpL = (+p, -p)"
(*uncommentR?Structure_ImpL*)*)
(*(*uncommentL?Structure_ImpR*) 
 | "structure_Op_polarity Structure_ImpR = (-p, +p)"
(*uncommentR?Structure_ImpR*)*)


(*we assume the structure appears in the sequent exactly once*)
fun polarity_Structure :: "Structure \<Rightarrow> Structure \<Rightarrow> polarity" where
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) 
"polarity_Structure s (Structure_Bin l oper r) = (
  if l = s then prod.fst (structure_Op_polarity oper)
  else if r = s then prod.snd (structure_Op_polarity oper)
  else ((prod.fst (structure_Op_polarity oper)) \<and>p (polarity_Structure s l)) \<or>p ((prod.snd (structure_Op_polarity oper)) \<and>p (polarity_Structure s r)) )" | 
(*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Action_Structure*) "polarity_Structure s (Structure_Action_Structure oper ac struct) = (polarity_Structure s struct)" | (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) "polarity_Structure s (Structure_Agent_Structure oper ag struct) = (polarity_Structure s struct)" | (*uncommentR?Structure_Agent_Structure*)*)
"polarity_Structure s x = (if s = x then +p else N)"


fun polarity_Sequent :: "Structure \<Rightarrow> Sequent \<Rightarrow> polarity" where
"polarity_Sequent s (Sequent lhs rhs) = (\<not>p(polarity_Structure s lhs)) \<or>p (polarity_Structure s rhs)" |
"polarity_Sequent s _ = N"

fun partial_goal :: "Structure \<Rightarrow> Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) 
"partial_goal s (Structure_Bin l oper r) = (case (polarity_Structure s l) of N \<Rightarrow> (if s = l then l else r) | _ \<Rightarrow> l)" |
(*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Action_Structure*) "partial_goal s (Structure_Action_Structure oper ac struct) = struct" | (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) "partial_goal s (Structure_Agent_Structure oper ag struct) = struct" | (*uncommentR?Structure_Agent_Structure*)*)
"partial_goal s x = x"

fun partial_goal_complement :: "Structure \<Rightarrow> Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) 
"partial_goal_complement s (Structure_Bin l oper r) = (case (polarity_Structure s l) of N \<Rightarrow> (if s = l then r else l) | _ \<Rightarrow> r)" |
(*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Action_Structure*) "partial_goal_complement s (Structure_Action_Structure oper ac struct) = struct" | (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) "partial_goal_complement s (Structure_Agent_Structure oper ag struct) = struct" | (*uncommentR?Structure_Agent_Structure*)*)
"partial_goal_complement s x = x"


lemma partial_goal:
  fixes oper x y s
  shows "((partial_goal s (Structure_Bin x oper y)) = x) \<or> (partial_goal s (Structure_Bin x oper y)) = y"
proof auto
assume "s = x" "(case polarity_Structure x x of +p \<Rightarrow> x | _ \<Rightarrow> x) \<noteq> y"
then show "(case polarity_Structure x x of +p \<Rightarrow> x | _ \<Rightarrow> x) = x" by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
next
assume "s \<noteq> x" "(case polarity_Structure s x of N \<Rightarrow> y | _ \<Rightarrow> x) \<noteq> y"
then show "(case polarity_Structure s x of N \<Rightarrow> y | _ \<Rightarrow> x) = x" by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
qed

lemma partial_goal_complement:
  fixes oper x y s
  shows "((partial_goal_complement s (Structure_Bin x oper y)) = x) \<or> (partial_goal_complement s (Structure_Bin x oper y)) = y"
proof auto
assume "s = x" "(case polarity_Structure x x of +p \<Rightarrow> y | _ \<Rightarrow> y) \<noteq> y"
then show "(case polarity_Structure x x of +p \<Rightarrow> y | _ \<Rightarrow> y) = x"
  by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
next
assume "s \<noteq> x" "(case polarity_Structure s x of N \<Rightarrow> x | _ \<Rightarrow> y) \<noteq> y"
then show "(case polarity_Structure s x of N \<Rightarrow> x | _ \<Rightarrow> y) = x" by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
qed


lemma partial_goal_and_complement:
  fixes oper x y s
  defines "struct \<equiv> Structure_Bin x oper y"
  shows "( (partial_goal s struct) = x \<and> (partial_goal_complement s struct) = y ) \<or> 
         ( (partial_goal_complement s struct) = x \<and> (partial_goal s struct) = y )"
using struct_def
apply auto
apply (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))+
done


fun position_in_Sequent :: "Structure \<Rightarrow> Sequent \<Rightarrow> polarity" where
"position_in_Sequent s (Sequent l r) = (
  if s = l then -p
  else if (polarity_Structure s l) \<noteq> N then -p
  else if s = r then +p 
  else if (polarity_Structure s r) \<noteq> N then +p
  else N )" |
"position_in_Sequent s _ = N"




fun fresh_name_aux :: "string list \<Rightarrow> string \<Rightarrow> string set \<Rightarrow> string" where
"fresh_name_aux [] s _ = s" |
"fresh_name_aux (x#xs) s full = (if (s@x) \<notin> full then s@x else (fresh_name_aux xs (s@x) full) )"


definition fresh_name :: "string list \<Rightarrow> string" where
"fresh_name list = fresh_name_aux list ''X'' (set list)"


fun collect_SFAtprop_names :: "Structure \<Rightarrow> string list" where
(*(*uncommentL?Structure_Formula?Formula_Atprop?Atprop-BEGIN*)*)(*uncommentL?Structure_Formula?Formula_Atprop?Atprop-END*)  "collect_SFAtprop_names (Structure_Formula (Formula_Atprop (Atprop x))) = [x]" |(*uncommentR?Structure_Formula?Formula_Atprop?Atprop-BEGIN*)(*(*uncommentR?Structure_Formula?Formula_Atprop?Atprop-END*)*)
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) "collect_SFAtprop_names (Structure_Bin l oper r) = (collect_SFAtprop_names l) @ (collect_SFAtprop_names r)" | (*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Action_Structure*) "collect_SFAtprop_names (Structure_Action_Structure oper ac struct) = collect_SFAtprop_names struct" | (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) "collect_SFAtprop_names (Structure_Agent_Structure oper ag struct) = collect_SFAtprop_names struct" | (*uncommentR?Structure_Agent_Structure*)*)
"collect_SFAtprop_names s = []"

fun replace_SFAtprop_into_Structure :: "Structure \<Rightarrow> Structure \<Rightarrow> Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) "replace_SFAtprop_into_Structure sfa repl (Structure_Bin l oper r) = Structure_Bin (replace_SFAtprop_into_Structure sfa repl l) oper (replace_SFAtprop_into_Structure sfa repl r)" | (*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Action_Structure*) "replace_SFAtprop_into_Structure sfa repl (Structure_Action_Structure oper ac struct) = Structure_Action_Structure oper ac (replace_SFAtprop_into_Structure sfa repl struct)" | (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) "replace_SFAtprop_into_Structure sfa repl (Structure_Agent_Structure oper ag struct) = Structure_Agent_Structure oper ag (replace_SFAtprop_into_Structure sfa repl struct)" | (*uncommentR?Structure_Agent_Structure*)*)
"replace_SFAtprop_into_Structure sfa repl s = (if sfa = s then repl else s)"


fun replace_SFAtprop_into_Sequent :: "Structure \<Rightarrow> Structure \<Rightarrow> Sequent \<Rightarrow> Sequent" where
"replace_SFAtprop_into_Sequent sfa repl (Sequent l r) = Sequent (replace_SFAtprop_into_Structure sfa repl l) (replace_SFAtprop_into_Structure sfa repl r)" |
"replace_SFAtprop_into_Sequent sfa relp x = x"

fun replace_SFAtprop_into_PT :: "Structure \<Rightarrow> Structure \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replace_SFAtprop_into_PT sfa repl (Prooftree s r list) = (Prooftree (replace_SFAtprop_into_Sequent sfa repl s) r (map (replace_SFAtprop_into_PT sfa repl) list))"


fun sequent_fresh_name :: "Sequent \<Rightarrow> Structure" where
"sequent_fresh_name (Sequent l r) = (Structure_Formula (Formula_Atprop (Atprop (fresh_name ((collect_SFAtprop_names l)@(collect_SFAtprop_names r)) ))))" |
"sequent_fresh_name _ = (Structure_Formula (Formula_Atprop (Atprop ''X'')))"



export_code open der isProofTree ruleList displayRules ant consq rulifyProoftree replaceIntoPT isProofTreeWithCut 
expandProoftree polarity_Sequent position_in_Sequent partial_goal partial_goal_complement sequent_fresh_name replace_SFAtprop_into_PT in Scala
module_name (*calc_name-BEGIN*)SequentCalc(*calc_name-END*) file (*export_path-BEGIN*)"../scala/SequentCalc.scala"(*export_path-END*)
end