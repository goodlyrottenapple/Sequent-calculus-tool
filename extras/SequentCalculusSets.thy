theory SequentCalculusSets
imports Main "../src/isabelle/SequentCalc_Core_SE"
begin


datatype sequentSets = sequent "Formula set" "Formula set" (infix "\<turnstile>" 300)


definition un :: "Formula set \<Rightarrow> Formula \<Rightarrow> Formula set" (infix ";;" 400) where
"un s e = insert e s"



inductive derivable :: "Formula list \<Rightarrow> sequentSets \<Rightarrow> bool"  ("_ \<turnstile>DS _" 310) where 
Not_L: "loc \<turnstile>DS (X \<turnstile> Y ;; A) \<Longrightarrow> loc \<turnstile>DS (X ;; (\<not>\<^sub>FA) \<turnstile> Y)"|
And_L: "loc \<turnstile>DS ((X ;; A) ;; B \<turnstile> Z) \<Longrightarrow> loc \<turnstile>DS (X ;; (A \<and>\<^sub>F B) \<turnstile> Z)"|
ImpR_R: "loc \<turnstile>DS (Z ;; A \<turnstile> X ;; B) \<Longrightarrow> loc \<turnstile>DS (Z \<turnstile> X ;; (A \<rightarrow>\<^sub>F B))"|
Or_L: "loc \<turnstile>DS (Z ;; B \<turnstile> W) \<Longrightarrow> loc \<turnstile>DS (X ;; A \<turnstile> Y) \<Longrightarrow> loc \<turnstile>DS (X ;; (A \<or>\<^sub>F B) \<turnstile> Y)"|
Not_R: "loc \<turnstile>DS (X ;; A \<turnstile> Y) \<Longrightarrow> loc \<turnstile>DS (X \<turnstile> Y ;; (\<not>\<^sub>F A))"|
ImpR_L: "loc \<turnstile>DS (X ;; B \<turnstile> Y) \<Longrightarrow> loc \<turnstile>DS (X \<turnstile> Y ;; A) \<Longrightarrow> loc \<turnstile>DS (X ;; (A \<rightarrow>\<^sub>F B) \<turnstile> Y)"|
And_R: "loc \<turnstile>DS (X \<turnstile> Y ;; B) \<Longrightarrow> loc \<turnstile>DS (X \<turnstile> Y ;; A) \<Longrightarrow> loc \<turnstile>DS (X \<turnstile> Y ;; (A \<and>\<^sub>F B))" |
Or_R: "loc \<turnstile>DS (Z \<turnstile> (X ;; A) ;; B) \<Longrightarrow> loc \<turnstile>DS (Z \<turnstile> X ;; (A \<or>\<^sub>F B))" |

Id: "X \<inter> Y \<noteq> {} \<Longrightarrow> loc \<turnstile>DS (X \<turnstile> Y)"|
Cut: "f \<in> set loc \<Longrightarrow> loc \<turnstile>DS (X ;; f \<turnstile> Y) \<Longrightarrow> loc \<turnstile>DS (X \<turnstile> Y ;; f) \<Longrightarrow> loc \<turnstile>DS (X \<turnstile> Y)"
end