theory SequentCalculus
imports Main "../src/isabelle/SequentCalc_Core_SE"
begin


datatype sequent = sequent "Formula list" "Formula list" (infix "\<turnstile>" 300)


definition concat :: "Formula list \<Rightarrow> Formula list \<Rightarrow> Formula list" (infix ";" 400) where
"concat list1 list2 = list1 @ list2"



inductive derivable' :: "sequent \<Rightarrow> bool"  ("\<turnstile>D _" 310) where 
Not_L: "\<turnstile>D (X \<turnstile> [A] ; Y) \<Longrightarrow> \<turnstile>D (X ; [\<not>\<^sub>FA] \<turnstile> Y)"|
And_L_1: "\<turnstile>D (X ; [A] \<turnstile> Z) \<Longrightarrow> \<turnstile>D (X ; [A \<and>\<^sub>F B] \<turnstile> Z)"|
And_L_2: "\<turnstile>D (X ; [B] \<turnstile> Z) \<Longrightarrow> \<turnstile>D (X ; [A \<and>\<^sub>F B] \<turnstile> Z)"|
ImpR_R: "\<turnstile>D (Z ; [A] \<turnstile> [B] ; X) \<Longrightarrow> \<turnstile>D (Z \<turnstile> [A \<rightarrow>\<^sub>F B] ; X)"|
Or_L: "\<turnstile>D (Z ; [B] \<turnstile> W) \<Longrightarrow> \<turnstile>D (X ; [A] \<turnstile> Y) \<Longrightarrow> \<turnstile>D ((X ; Z) ; [A \<or>\<^sub>F B] \<turnstile> Y ; W)"|
Not_R: "\<turnstile>D (X ; [A] \<turnstile> Y) \<Longrightarrow> \<turnstile>D (X \<turnstile> [\<not>\<^sub>F A] ; Y)"|
ImpR_L: "\<turnstile>D (Z ; [B] \<turnstile> W) \<Longrightarrow> \<turnstile>D (X \<turnstile> [A] ; Y) \<Longrightarrow> \<turnstile>D ((X ; Z) ; [A \<rightarrow>\<^sub>F B] \<turnstile> Y ; W)"|
And_R: "\<turnstile>D (Z \<turnstile> [B] ; W) \<Longrightarrow> \<turnstile>D (X \<turnstile> [A] ; Y) \<Longrightarrow> \<turnstile>D (X ; Z \<turnstile> [A \<and>\<^sub>F B] ; (Y ; W))"|
Or_R_2: "\<turnstile>D (Z \<turnstile> [B] ; X) \<Longrightarrow> \<turnstile>D (Z \<turnstile> [A \<or>\<^sub>F B] ; X)"|
Or_R_1: "\<turnstile>D (Z \<turnstile> [A] ; X) \<Longrightarrow> \<turnstile>D (Z \<turnstile> [A \<or>\<^sub>F B] ; X)"
| 
W_L: "\<turnstile>D (X \<turnstile> Y) \<Longrightarrow> \<turnstile>D (X ; [A] \<turnstile> Y)"|
P_L: "\<turnstile>D ((X1 ; [A]) ; ([B] ; X2) \<turnstile> Y) \<Longrightarrow> \<turnstile>D ((X1 ; [B]) ; ([A] ; X2) \<turnstile> Y)"|

C_L: "\<turnstile>D ((X ; [A]) ; [A] \<turnstile> Y) \<Longrightarrow> \<turnstile>D (X ; [A] \<turnstile> Y)"|
C_R: "\<turnstile>D (X \<turnstile> ([A] ; [A]) ; Y) \<Longrightarrow> \<turnstile>D (X \<turnstile> [A] ; Y)"|

P_R: "\<turnstile>D (X \<turnstile> (Y1 ; [A]) ; ([B] ; Y2)) \<Longrightarrow> \<turnstile>D (X \<turnstile> (Y1 ; [B]) ; ([A] ; Y2))"|
W_R: "\<turnstile>D (X \<turnstile> Y) \<Longrightarrow> \<turnstile>D (X \<turnstile> [A] ; Y)"
| 
Id: "\<turnstile>D ([f] \<turnstile> [f])"

end