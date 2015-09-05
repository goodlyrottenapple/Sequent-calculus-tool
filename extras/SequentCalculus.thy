theory SequentCalculus
imports Main "../src/isabelle/SequentCalc_Core_SE"
begin


datatype sequent = sequent "Formula list" "Formula list" (infix "\<turnstile>" 300)


definition concat :: "Formula list \<Rightarrow> Formula list \<Rightarrow> Formula list" (infix ";" 400) where
"concat list1 list2 = list1 @ list2"



inductive derivable' :: "Formula list \<Rightarrow> sequent \<Rightarrow> bool"  ("_ \<turnstile>D _" 310) where 
Not_L: "loc \<turnstile>D (X \<turnstile> [A] ; Y) \<Longrightarrow> loc \<turnstile>D (X ; [\<not>\<^sub>FA] \<turnstile> Y)"|
And_L_1: "loc \<turnstile>D (X ; [A] \<turnstile> Z) \<Longrightarrow> loc \<turnstile>D (X ; [A \<and>\<^sub>F B] \<turnstile> Z)"|
And_L_2: "loc \<turnstile>D (X ; [B] \<turnstile> Z) \<Longrightarrow> loc \<turnstile>D (X ; [A \<and>\<^sub>F B] \<turnstile> Z)"|
ImpR_R: "loc \<turnstile>D (Z ; [A] \<turnstile> [B] ; X) \<Longrightarrow> loc \<turnstile>D (Z \<turnstile> [A \<rightarrow>\<^sub>F B] ; X)"|
Or_L: "loc \<turnstile>D (Z ; [B] \<turnstile> W) \<Longrightarrow> loc \<turnstile>D (X ; [A] \<turnstile> Y) \<Longrightarrow> loc \<turnstile>D ((X ; Z) ; [A \<or>\<^sub>F B] \<turnstile> Y ; W)"|
Not_R: "loc \<turnstile>D (X ; [A] \<turnstile> Y) \<Longrightarrow> loc \<turnstile>D (X \<turnstile> [\<not>\<^sub>F A] ; Y)"|
ImpR_L: "loc \<turnstile>D (Z ; [B] \<turnstile> W) \<Longrightarrow> loc \<turnstile>D (X \<turnstile> [A] ; Y) \<Longrightarrow> loc \<turnstile>D ((X ; Z) ; [A \<rightarrow>\<^sub>F B] \<turnstile> Y ; W)"|
And_R: "loc \<turnstile>D (Z \<turnstile> [B] ; W) \<Longrightarrow> loc \<turnstile>D (X \<turnstile> [A] ; Y) \<Longrightarrow> loc \<turnstile>D (X ; Z \<turnstile> [A \<and>\<^sub>F B] ; (Y ; W))"|
Or_R_2: "loc \<turnstile>D (Z \<turnstile> [B] ; X) \<Longrightarrow> loc \<turnstile>D (Z \<turnstile> [A \<or>\<^sub>F B] ; X)"|
Or_R_1: "loc \<turnstile>D (Z \<turnstile> [A] ; X) \<Longrightarrow> loc \<turnstile>D (Z \<turnstile> [A \<or>\<^sub>F B] ; X)"
| 
W_L: "loc \<turnstile>D (X \<turnstile> Y) \<Longrightarrow> loc \<turnstile>D (X ; [A] \<turnstile> Y)"|
P_L: "loc \<turnstile>D ((X1 ; [A]) ; ([B] ; X2) \<turnstile> Y) \<Longrightarrow> loc \<turnstile>D ((X1 ; [B]) ; ([A] ; X2) \<turnstile> Y)"|

C_L: "loc \<turnstile>D ((X ; [A]) ; [A] \<turnstile> Y) \<Longrightarrow> loc \<turnstile>D (X ; [A] \<turnstile> Y)"|
C_R: "loc \<turnstile>D (X \<turnstile> ([A] ; [A]) ; Y) \<Longrightarrow> loc \<turnstile>D (X \<turnstile> [A] ; Y)"|

P_R: "loc \<turnstile>D (X \<turnstile> (Y1 ; [A]) ; ([B] ; Y2)) \<Longrightarrow> loc \<turnstile>D (X \<turnstile> (Y1 ; [B]) ; ([A] ; Y2))"|
W_R: "loc \<turnstile>D (X \<turnstile> Y) \<Longrightarrow> loc \<turnstile>D (X \<turnstile> [A] ; Y)"
| 
Id: "loc \<turnstile>D ([f] \<turnstile> [f])"|
Cut: "f \<in> set loc \<Longrightarrow> loc \<turnstile>D ([f] ; W \<turnstile> Y) \<Longrightarrow> loc \<turnstile>D (X \<turnstile> Z ; [f]) \<Longrightarrow> loc \<turnstile>D (X ; W \<turnstile> Z ; Y)"


end