theory (*calc_name_core_se-BEGIN*)SequentCalc_Core_SE(*calc_name_core_se-END*)
imports Main
begin

(*calc_structure_se-BEGIN*)
type_synonym Atprop = string

datatype Formula = Formula_Atprop Atprop ("_ \<^sub>A" [320] 330)
                 | Formula_Or Formula Formula (infix "\<or>\<^sub>F" 330)
                 | Formula_ImpR Formula Formula (infix "\<rightarrow>\<^sub>F" 330)
                 | Formula_And Formula Formula (infix "\<and>\<^sub>F" 330)
                 | Formula_Not Formula ("\<not>\<^sub>F _" [] 331)

datatype Structure = Structure_Comma Structure Structure (infix ",\<^sub>S" 340)
                   | Structure_Formula Formula ("_ \<^sub>S" [330] 340)
                   | Structure_Empty ("I")

datatype Sequent = Sequent Structure Structure ("_ \<turnstile>\<^sub>S _" [311,311] 310)
                 | Sequent_Structure Structure
(*calc_structure_se-END*)


end