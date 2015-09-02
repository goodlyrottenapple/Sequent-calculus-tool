object SequentCalc {

def equal_boola(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

trait equal[A] {
  val `SequentCalc.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean =
  A.`SequentCalc.equal`(a, b)

implicit def equal_bool: equal[Boolean] = new equal[Boolean] {
  val `SequentCalc.equal` = (a: Boolean, b: Boolean) => equal_boola(a, b)
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

def equal_lista[A : equal](x0: List[A], x1: List[A]): Boolean = (x0, x1) match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) => eq[A](x21, y21) && equal_lista[A](x22, y22)
  case (Nil, Nil) => true
}

implicit def equal_list[A : equal]: equal[List[A]] = new equal[List[A]] {
  val `SequentCalc.equal` = (a: List[A], b: List[A]) => equal_lista[A](a, b)
}

implicit def equal_char: equal[Char] = new equal[Char] {
  val `SequentCalc.equal` = (a: Char, b: Char) => a == b
}

abstract sealed class Structure_Zer_Op
final case class Structure_Empty() extends Structure_Zer_Op

def equal_Structure_Zer_Op(x0: Structure_Zer_Op, x1: Structure_Zer_Op): Boolean
  =
  (x0, x1) match {
  case (Structure_Empty(), Structure_Empty()) => true
}

abstract sealed class Structure_Bin_Op
final case class Structure_Comma() extends Structure_Bin_Op

def equal_Structure_Bin_Op(x0: Structure_Bin_Op, x1: Structure_Bin_Op): Boolean
  =
  (x0, x1) match {
  case (Structure_Comma(), Structure_Comma()) => true
}

abstract sealed class Formula_Bin_Op
final case class Formula_And() extends Formula_Bin_Op
final case class Formula_ImpR() extends Formula_Bin_Op
final case class Formula_Or() extends Formula_Bin_Op

def equal_Formula_Bin_Op(x0: Formula_Bin_Op, x1: Formula_Bin_Op): Boolean =
  (x0, x1) match {
  case (Formula_ImpR(), Formula_Or()) => false
  case (Formula_Or(), Formula_ImpR()) => false
  case (Formula_And(), Formula_Or()) => false
  case (Formula_Or(), Formula_And()) => false
  case (Formula_And(), Formula_ImpR()) => false
  case (Formula_ImpR(), Formula_And()) => false
  case (Formula_Or(), Formula_Or()) => true
  case (Formula_ImpR(), Formula_ImpR()) => true
  case (Formula_And(), Formula_And()) => true
}

abstract sealed class Formula_Un_Op
final case class Formula_Not() extends Formula_Un_Op

def equal_Formula_Un_Op(x0: Formula_Un_Op, x1: Formula_Un_Op): Boolean =
  (x0, x1) match {
  case (Formula_Not(), Formula_Not()) => true
}

abstract sealed class Atprop
final case class Atpropa(a: List[Char]) extends Atprop
final case class Atprop_Freevar(a: List[Char]) extends Atprop

def equal_Atpropa(x0: Atprop, x1: Atprop): Boolean = (x0, x1) match {
  case (Atpropa(x1), Atprop_Freevar(x2)) => false
  case (Atprop_Freevar(x2), Atpropa(x1)) => false
  case (Atprop_Freevar(x2), Atprop_Freevar(y2)) => equal_lista[Char](x2, y2)
  case (Atpropa(x1), Atpropa(y1)) => equal_lista[Char](x1, y1)
}

abstract sealed class Formula
final case class Formula_Atprop(a: Atprop) extends Formula
final case class Formula_Bin(a: Formula, b: Formula_Bin_Op, c: Formula) extends
  Formula
final case class Formula_Freevar(a: List[Char]) extends Formula
final case class Formula_Un(a: Formula_Un_Op, b: Formula) extends Formula

def equal_Formulaa(x0: Formula, x1: Formula): Boolean = (x0, x1) match {
  case (Formula_Freevar(x3), Formula_Un(x41, x42)) => false
  case (Formula_Un(x41, x42), Formula_Freevar(x3)) => false
  case (Formula_Bin(x21, x22, x23), Formula_Un(x41, x42)) => false
  case (Formula_Un(x41, x42), Formula_Bin(x21, x22, x23)) => false
  case (Formula_Bin(x21, x22, x23), Formula_Freevar(x3)) => false
  case (Formula_Freevar(x3), Formula_Bin(x21, x22, x23)) => false
  case (Formula_Atprop(x1), Formula_Un(x41, x42)) => false
  case (Formula_Un(x41, x42), Formula_Atprop(x1)) => false
  case (Formula_Atprop(x1), Formula_Freevar(x3)) => false
  case (Formula_Freevar(x3), Formula_Atprop(x1)) => false
  case (Formula_Atprop(x1), Formula_Bin(x21, x22, x23)) => false
  case (Formula_Bin(x21, x22, x23), Formula_Atprop(x1)) => false
  case (Formula_Un(x41, x42), Formula_Un(y41, y42)) =>
    equal_Formula_Un_Op(x41, y41) && equal_Formulaa(x42, y42)
  case (Formula_Freevar(x3), Formula_Freevar(y3)) => equal_lista[Char](x3, y3)
  case (Formula_Bin(x21, x22, x23), Formula_Bin(y21, y22, y23)) =>
    equal_Formulaa(x21, y21) &&
      (equal_Formula_Bin_Op(x22, y22) && equal_Formulaa(x23, y23))
  case (Formula_Atprop(x1), Formula_Atprop(y1)) => equal_Atpropa(x1, y1)
}

abstract sealed class Structure
final case class Structure_Bin(a: Structure, b: Structure_Bin_Op, c: Structure)
  extends Structure
final case class Structure_Formula(a: Formula) extends Structure
final case class Structure_Freevar(a: List[Char]) extends Structure
final case class Structure_Zer(a: Structure_Zer_Op) extends Structure

def equal_Structurea(x0: Structure, x1: Structure): Boolean = (x0, x1) match {
  case (Structure_Freevar(x3), Structure_Zer(x4)) => false
  case (Structure_Zer(x4), Structure_Freevar(x3)) => false
  case (Structure_Formula(x2), Structure_Zer(x4)) => false
  case (Structure_Zer(x4), Structure_Formula(x2)) => false
  case (Structure_Formula(x2), Structure_Freevar(x3)) => false
  case (Structure_Freevar(x3), Structure_Formula(x2)) => false
  case (Structure_Bin(x11, x12, x13), Structure_Zer(x4)) => false
  case (Structure_Zer(x4), Structure_Bin(x11, x12, x13)) => false
  case (Structure_Bin(x11, x12, x13), Structure_Freevar(x3)) => false
  case (Structure_Freevar(x3), Structure_Bin(x11, x12, x13)) => false
  case (Structure_Bin(x11, x12, x13), Structure_Formula(x2)) => false
  case (Structure_Formula(x2), Structure_Bin(x11, x12, x13)) => false
  case (Structure_Zer(x4), Structure_Zer(y4)) => equal_Structure_Zer_Op(x4, y4)
  case (Structure_Freevar(x3), Structure_Freevar(y3)) =>
    equal_lista[Char](x3, y3)
  case (Structure_Formula(x2), Structure_Formula(y2)) => equal_Formulaa(x2, y2)
  case (Structure_Bin(x11, x12, x13), Structure_Bin(y11, y12, y13)) =>
    equal_Structurea(x11, y11) &&
      (equal_Structure_Bin_Op(x12, y12) && equal_Structurea(x13, y13))
}

abstract sealed class Sequent
final case class Sequenta(a: Structure, b: Structure) extends Sequent
final case class Sequent_Structure(a: Structure) extends Sequent

def equal_Sequenta(x0: Sequent, x1: Sequent): Boolean = (x0, x1) match {
  case (Sequenta(x11, x12), Sequent_Structure(x2)) => false
  case (Sequent_Structure(x2), Sequenta(x11, x12)) => false
  case (Sequent_Structure(x2), Sequent_Structure(y2)) =>
    equal_Structurea(x2, y2)
  case (Sequenta(x11, x12), Sequenta(y11, y12)) =>
    equal_Structurea(x11, y11) && equal_Structurea(x12, y12)
}

abstract sealed class RuleStruct
final case class A_L() extends RuleStruct
final case class A_L2() extends RuleStruct
final case class A_R() extends RuleStruct
final case class A_R2() extends RuleStruct
final case class C_L() extends RuleStruct
final case class C_R() extends RuleStruct
final case class I_L_L() extends RuleStruct
final case class I_L_L2() extends RuleStruct
final case class I_L_R() extends RuleStruct
final case class I_L_R2() extends RuleStruct
final case class I_R_L() extends RuleStruct
final case class I_R_L2() extends RuleStruct
final case class I_R_R() extends RuleStruct
final case class I_R_R2() extends RuleStruct
final case class P_L() extends RuleStruct
final case class P_R() extends RuleStruct
final case class W_L() extends RuleStruct
final case class W_R() extends RuleStruct

def equal_RuleStruct(x0: RuleStruct, x1: RuleStruct): Boolean = (x0, x1) match {
  case (W_L(), W_R()) => false
  case (W_R(), W_L()) => false
  case (P_R(), W_R()) => false
  case (W_R(), P_R()) => false
  case (P_R(), W_L()) => false
  case (W_L(), P_R()) => false
  case (P_L(), W_R()) => false
  case (W_R(), P_L()) => false
  case (P_L(), W_L()) => false
  case (W_L(), P_L()) => false
  case (P_L(), P_R()) => false
  case (P_R(), P_L()) => false
  case (I_R_R2(), W_R()) => false
  case (W_R(), I_R_R2()) => false
  case (I_R_R2(), W_L()) => false
  case (W_L(), I_R_R2()) => false
  case (I_R_R2(), P_R()) => false
  case (P_R(), I_R_R2()) => false
  case (I_R_R2(), P_L()) => false
  case (P_L(), I_R_R2()) => false
  case (I_R_R(), W_R()) => false
  case (W_R(), I_R_R()) => false
  case (I_R_R(), W_L()) => false
  case (W_L(), I_R_R()) => false
  case (I_R_R(), P_R()) => false
  case (P_R(), I_R_R()) => false
  case (I_R_R(), P_L()) => false
  case (P_L(), I_R_R()) => false
  case (I_R_R(), I_R_R2()) => false
  case (I_R_R2(), I_R_R()) => false
  case (I_R_L2(), W_R()) => false
  case (W_R(), I_R_L2()) => false
  case (I_R_L2(), W_L()) => false
  case (W_L(), I_R_L2()) => false
  case (I_R_L2(), P_R()) => false
  case (P_R(), I_R_L2()) => false
  case (I_R_L2(), P_L()) => false
  case (P_L(), I_R_L2()) => false
  case (I_R_L2(), I_R_R2()) => false
  case (I_R_R2(), I_R_L2()) => false
  case (I_R_L2(), I_R_R()) => false
  case (I_R_R(), I_R_L2()) => false
  case (I_R_L(), W_R()) => false
  case (W_R(), I_R_L()) => false
  case (I_R_L(), W_L()) => false
  case (W_L(), I_R_L()) => false
  case (I_R_L(), P_R()) => false
  case (P_R(), I_R_L()) => false
  case (I_R_L(), P_L()) => false
  case (P_L(), I_R_L()) => false
  case (I_R_L(), I_R_R2()) => false
  case (I_R_R2(), I_R_L()) => false
  case (I_R_L(), I_R_R()) => false
  case (I_R_R(), I_R_L()) => false
  case (I_R_L(), I_R_L2()) => false
  case (I_R_L2(), I_R_L()) => false
  case (I_L_R2(), W_R()) => false
  case (W_R(), I_L_R2()) => false
  case (I_L_R2(), W_L()) => false
  case (W_L(), I_L_R2()) => false
  case (I_L_R2(), P_R()) => false
  case (P_R(), I_L_R2()) => false
  case (I_L_R2(), P_L()) => false
  case (P_L(), I_L_R2()) => false
  case (I_L_R2(), I_R_R2()) => false
  case (I_R_R2(), I_L_R2()) => false
  case (I_L_R2(), I_R_R()) => false
  case (I_R_R(), I_L_R2()) => false
  case (I_L_R2(), I_R_L2()) => false
  case (I_R_L2(), I_L_R2()) => false
  case (I_L_R2(), I_R_L()) => false
  case (I_R_L(), I_L_R2()) => false
  case (I_L_R(), W_R()) => false
  case (W_R(), I_L_R()) => false
  case (I_L_R(), W_L()) => false
  case (W_L(), I_L_R()) => false
  case (I_L_R(), P_R()) => false
  case (P_R(), I_L_R()) => false
  case (I_L_R(), P_L()) => false
  case (P_L(), I_L_R()) => false
  case (I_L_R(), I_R_R2()) => false
  case (I_R_R2(), I_L_R()) => false
  case (I_L_R(), I_R_R()) => false
  case (I_R_R(), I_L_R()) => false
  case (I_L_R(), I_R_L2()) => false
  case (I_R_L2(), I_L_R()) => false
  case (I_L_R(), I_R_L()) => false
  case (I_R_L(), I_L_R()) => false
  case (I_L_R(), I_L_R2()) => false
  case (I_L_R2(), I_L_R()) => false
  case (I_L_L2(), W_R()) => false
  case (W_R(), I_L_L2()) => false
  case (I_L_L2(), W_L()) => false
  case (W_L(), I_L_L2()) => false
  case (I_L_L2(), P_R()) => false
  case (P_R(), I_L_L2()) => false
  case (I_L_L2(), P_L()) => false
  case (P_L(), I_L_L2()) => false
  case (I_L_L2(), I_R_R2()) => false
  case (I_R_R2(), I_L_L2()) => false
  case (I_L_L2(), I_R_R()) => false
  case (I_R_R(), I_L_L2()) => false
  case (I_L_L2(), I_R_L2()) => false
  case (I_R_L2(), I_L_L2()) => false
  case (I_L_L2(), I_R_L()) => false
  case (I_R_L(), I_L_L2()) => false
  case (I_L_L2(), I_L_R2()) => false
  case (I_L_R2(), I_L_L2()) => false
  case (I_L_L2(), I_L_R()) => false
  case (I_L_R(), I_L_L2()) => false
  case (I_L_L(), W_R()) => false
  case (W_R(), I_L_L()) => false
  case (I_L_L(), W_L()) => false
  case (W_L(), I_L_L()) => false
  case (I_L_L(), P_R()) => false
  case (P_R(), I_L_L()) => false
  case (I_L_L(), P_L()) => false
  case (P_L(), I_L_L()) => false
  case (I_L_L(), I_R_R2()) => false
  case (I_R_R2(), I_L_L()) => false
  case (I_L_L(), I_R_R()) => false
  case (I_R_R(), I_L_L()) => false
  case (I_L_L(), I_R_L2()) => false
  case (I_R_L2(), I_L_L()) => false
  case (I_L_L(), I_R_L()) => false
  case (I_R_L(), I_L_L()) => false
  case (I_L_L(), I_L_R2()) => false
  case (I_L_R2(), I_L_L()) => false
  case (I_L_L(), I_L_R()) => false
  case (I_L_R(), I_L_L()) => false
  case (I_L_L(), I_L_L2()) => false
  case (I_L_L2(), I_L_L()) => false
  case (C_R(), W_R()) => false
  case (W_R(), C_R()) => false
  case (C_R(), W_L()) => false
  case (W_L(), C_R()) => false
  case (C_R(), P_R()) => false
  case (P_R(), C_R()) => false
  case (C_R(), P_L()) => false
  case (P_L(), C_R()) => false
  case (C_R(), I_R_R2()) => false
  case (I_R_R2(), C_R()) => false
  case (C_R(), I_R_R()) => false
  case (I_R_R(), C_R()) => false
  case (C_R(), I_R_L2()) => false
  case (I_R_L2(), C_R()) => false
  case (C_R(), I_R_L()) => false
  case (I_R_L(), C_R()) => false
  case (C_R(), I_L_R2()) => false
  case (I_L_R2(), C_R()) => false
  case (C_R(), I_L_R()) => false
  case (I_L_R(), C_R()) => false
  case (C_R(), I_L_L2()) => false
  case (I_L_L2(), C_R()) => false
  case (C_R(), I_L_L()) => false
  case (I_L_L(), C_R()) => false
  case (C_L(), W_R()) => false
  case (W_R(), C_L()) => false
  case (C_L(), W_L()) => false
  case (W_L(), C_L()) => false
  case (C_L(), P_R()) => false
  case (P_R(), C_L()) => false
  case (C_L(), P_L()) => false
  case (P_L(), C_L()) => false
  case (C_L(), I_R_R2()) => false
  case (I_R_R2(), C_L()) => false
  case (C_L(), I_R_R()) => false
  case (I_R_R(), C_L()) => false
  case (C_L(), I_R_L2()) => false
  case (I_R_L2(), C_L()) => false
  case (C_L(), I_R_L()) => false
  case (I_R_L(), C_L()) => false
  case (C_L(), I_L_R2()) => false
  case (I_L_R2(), C_L()) => false
  case (C_L(), I_L_R()) => false
  case (I_L_R(), C_L()) => false
  case (C_L(), I_L_L2()) => false
  case (I_L_L2(), C_L()) => false
  case (C_L(), I_L_L()) => false
  case (I_L_L(), C_L()) => false
  case (C_L(), C_R()) => false
  case (C_R(), C_L()) => false
  case (A_R2(), W_R()) => false
  case (W_R(), A_R2()) => false
  case (A_R2(), W_L()) => false
  case (W_L(), A_R2()) => false
  case (A_R2(), P_R()) => false
  case (P_R(), A_R2()) => false
  case (A_R2(), P_L()) => false
  case (P_L(), A_R2()) => false
  case (A_R2(), I_R_R2()) => false
  case (I_R_R2(), A_R2()) => false
  case (A_R2(), I_R_R()) => false
  case (I_R_R(), A_R2()) => false
  case (A_R2(), I_R_L2()) => false
  case (I_R_L2(), A_R2()) => false
  case (A_R2(), I_R_L()) => false
  case (I_R_L(), A_R2()) => false
  case (A_R2(), I_L_R2()) => false
  case (I_L_R2(), A_R2()) => false
  case (A_R2(), I_L_R()) => false
  case (I_L_R(), A_R2()) => false
  case (A_R2(), I_L_L2()) => false
  case (I_L_L2(), A_R2()) => false
  case (A_R2(), I_L_L()) => false
  case (I_L_L(), A_R2()) => false
  case (A_R2(), C_R()) => false
  case (C_R(), A_R2()) => false
  case (A_R2(), C_L()) => false
  case (C_L(), A_R2()) => false
  case (A_R(), W_R()) => false
  case (W_R(), A_R()) => false
  case (A_R(), W_L()) => false
  case (W_L(), A_R()) => false
  case (A_R(), P_R()) => false
  case (P_R(), A_R()) => false
  case (A_R(), P_L()) => false
  case (P_L(), A_R()) => false
  case (A_R(), I_R_R2()) => false
  case (I_R_R2(), A_R()) => false
  case (A_R(), I_R_R()) => false
  case (I_R_R(), A_R()) => false
  case (A_R(), I_R_L2()) => false
  case (I_R_L2(), A_R()) => false
  case (A_R(), I_R_L()) => false
  case (I_R_L(), A_R()) => false
  case (A_R(), I_L_R2()) => false
  case (I_L_R2(), A_R()) => false
  case (A_R(), I_L_R()) => false
  case (I_L_R(), A_R()) => false
  case (A_R(), I_L_L2()) => false
  case (I_L_L2(), A_R()) => false
  case (A_R(), I_L_L()) => false
  case (I_L_L(), A_R()) => false
  case (A_R(), C_R()) => false
  case (C_R(), A_R()) => false
  case (A_R(), C_L()) => false
  case (C_L(), A_R()) => false
  case (A_R(), A_R2()) => false
  case (A_R2(), A_R()) => false
  case (A_L2(), W_R()) => false
  case (W_R(), A_L2()) => false
  case (A_L2(), W_L()) => false
  case (W_L(), A_L2()) => false
  case (A_L2(), P_R()) => false
  case (P_R(), A_L2()) => false
  case (A_L2(), P_L()) => false
  case (P_L(), A_L2()) => false
  case (A_L2(), I_R_R2()) => false
  case (I_R_R2(), A_L2()) => false
  case (A_L2(), I_R_R()) => false
  case (I_R_R(), A_L2()) => false
  case (A_L2(), I_R_L2()) => false
  case (I_R_L2(), A_L2()) => false
  case (A_L2(), I_R_L()) => false
  case (I_R_L(), A_L2()) => false
  case (A_L2(), I_L_R2()) => false
  case (I_L_R2(), A_L2()) => false
  case (A_L2(), I_L_R()) => false
  case (I_L_R(), A_L2()) => false
  case (A_L2(), I_L_L2()) => false
  case (I_L_L2(), A_L2()) => false
  case (A_L2(), I_L_L()) => false
  case (I_L_L(), A_L2()) => false
  case (A_L2(), C_R()) => false
  case (C_R(), A_L2()) => false
  case (A_L2(), C_L()) => false
  case (C_L(), A_L2()) => false
  case (A_L2(), A_R2()) => false
  case (A_R2(), A_L2()) => false
  case (A_L2(), A_R()) => false
  case (A_R(), A_L2()) => false
  case (A_L(), W_R()) => false
  case (W_R(), A_L()) => false
  case (A_L(), W_L()) => false
  case (W_L(), A_L()) => false
  case (A_L(), P_R()) => false
  case (P_R(), A_L()) => false
  case (A_L(), P_L()) => false
  case (P_L(), A_L()) => false
  case (A_L(), I_R_R2()) => false
  case (I_R_R2(), A_L()) => false
  case (A_L(), I_R_R()) => false
  case (I_R_R(), A_L()) => false
  case (A_L(), I_R_L2()) => false
  case (I_R_L2(), A_L()) => false
  case (A_L(), I_R_L()) => false
  case (I_R_L(), A_L()) => false
  case (A_L(), I_L_R2()) => false
  case (I_L_R2(), A_L()) => false
  case (A_L(), I_L_R()) => false
  case (I_L_R(), A_L()) => false
  case (A_L(), I_L_L2()) => false
  case (I_L_L2(), A_L()) => false
  case (A_L(), I_L_L()) => false
  case (I_L_L(), A_L()) => false
  case (A_L(), C_R()) => false
  case (C_R(), A_L()) => false
  case (A_L(), C_L()) => false
  case (C_L(), A_L()) => false
  case (A_L(), A_R2()) => false
  case (A_R2(), A_L()) => false
  case (A_L(), A_R()) => false
  case (A_R(), A_L()) => false
  case (A_L(), A_L2()) => false
  case (A_L2(), A_L()) => false
  case (W_R(), W_R()) => true
  case (W_L(), W_L()) => true
  case (P_R(), P_R()) => true
  case (P_L(), P_L()) => true
  case (I_R_R2(), I_R_R2()) => true
  case (I_R_R(), I_R_R()) => true
  case (I_R_L2(), I_R_L2()) => true
  case (I_R_L(), I_R_L()) => true
  case (I_L_R2(), I_L_R2()) => true
  case (I_L_R(), I_L_R()) => true
  case (I_L_L2(), I_L_L2()) => true
  case (I_L_L(), I_L_L()) => true
  case (C_R(), C_R()) => true
  case (C_L(), C_L()) => true
  case (A_R2(), A_R2()) => true
  case (A_R(), A_R()) => true
  case (A_L2(), A_L2()) => true
  case (A_L(), A_L()) => true
}

abstract sealed class RuleZer
final case class Id() extends RuleZer
final case class Partial() extends RuleZer
final case class Prem() extends RuleZer

def equal_RuleZer(x0: RuleZer, x1: RuleZer): Boolean = (x0, x1) match {
  case (Partial(), Prem()) => false
  case (Prem(), Partial()) => false
  case (Id(), Prem()) => false
  case (Prem(), Id()) => false
  case (Id(), Partial()) => false
  case (Partial(), Id()) => false
  case (Prem(), Prem()) => true
  case (Partial(), Partial()) => true
  case (Id(), Id()) => true
}

abstract sealed class RuleCut
final case class SingleCut() extends RuleCut

def equal_RuleCut(x0: RuleCut, x1: RuleCut): Boolean = (x0, x1) match {
  case (SingleCut(), SingleCut()) => true
}

abstract sealed class RuleL
final case class And_L_1() extends RuleL
final case class And_L_2() extends RuleL
final case class And_R() extends RuleL
final case class ImpR_L() extends RuleL
final case class ImpR_R() extends RuleL
final case class Not_L() extends RuleL
final case class Not_R() extends RuleL
final case class Or_L() extends RuleL
final case class Or_R_1() extends RuleL
final case class Or_R_2() extends RuleL

def equal_RuleL(x0: RuleL, x1: RuleL): Boolean = (x0, x1) match {
  case (Or_R_1(), Or_R_2()) => false
  case (Or_R_2(), Or_R_1()) => false
  case (Or_L(), Or_R_2()) => false
  case (Or_R_2(), Or_L()) => false
  case (Or_L(), Or_R_1()) => false
  case (Or_R_1(), Or_L()) => false
  case (Not_R(), Or_R_2()) => false
  case (Or_R_2(), Not_R()) => false
  case (Not_R(), Or_R_1()) => false
  case (Or_R_1(), Not_R()) => false
  case (Not_R(), Or_L()) => false
  case (Or_L(), Not_R()) => false
  case (Not_L(), Or_R_2()) => false
  case (Or_R_2(), Not_L()) => false
  case (Not_L(), Or_R_1()) => false
  case (Or_R_1(), Not_L()) => false
  case (Not_L(), Or_L()) => false
  case (Or_L(), Not_L()) => false
  case (Not_L(), Not_R()) => false
  case (Not_R(), Not_L()) => false
  case (ImpR_R(), Or_R_2()) => false
  case (Or_R_2(), ImpR_R()) => false
  case (ImpR_R(), Or_R_1()) => false
  case (Or_R_1(), ImpR_R()) => false
  case (ImpR_R(), Or_L()) => false
  case (Or_L(), ImpR_R()) => false
  case (ImpR_R(), Not_R()) => false
  case (Not_R(), ImpR_R()) => false
  case (ImpR_R(), Not_L()) => false
  case (Not_L(), ImpR_R()) => false
  case (ImpR_L(), Or_R_2()) => false
  case (Or_R_2(), ImpR_L()) => false
  case (ImpR_L(), Or_R_1()) => false
  case (Or_R_1(), ImpR_L()) => false
  case (ImpR_L(), Or_L()) => false
  case (Or_L(), ImpR_L()) => false
  case (ImpR_L(), Not_R()) => false
  case (Not_R(), ImpR_L()) => false
  case (ImpR_L(), Not_L()) => false
  case (Not_L(), ImpR_L()) => false
  case (ImpR_L(), ImpR_R()) => false
  case (ImpR_R(), ImpR_L()) => false
  case (And_R(), Or_R_2()) => false
  case (Or_R_2(), And_R()) => false
  case (And_R(), Or_R_1()) => false
  case (Or_R_1(), And_R()) => false
  case (And_R(), Or_L()) => false
  case (Or_L(), And_R()) => false
  case (And_R(), Not_R()) => false
  case (Not_R(), And_R()) => false
  case (And_R(), Not_L()) => false
  case (Not_L(), And_R()) => false
  case (And_R(), ImpR_R()) => false
  case (ImpR_R(), And_R()) => false
  case (And_R(), ImpR_L()) => false
  case (ImpR_L(), And_R()) => false
  case (And_L_2(), Or_R_2()) => false
  case (Or_R_2(), And_L_2()) => false
  case (And_L_2(), Or_R_1()) => false
  case (Or_R_1(), And_L_2()) => false
  case (And_L_2(), Or_L()) => false
  case (Or_L(), And_L_2()) => false
  case (And_L_2(), Not_R()) => false
  case (Not_R(), And_L_2()) => false
  case (And_L_2(), Not_L()) => false
  case (Not_L(), And_L_2()) => false
  case (And_L_2(), ImpR_R()) => false
  case (ImpR_R(), And_L_2()) => false
  case (And_L_2(), ImpR_L()) => false
  case (ImpR_L(), And_L_2()) => false
  case (And_L_2(), And_R()) => false
  case (And_R(), And_L_2()) => false
  case (And_L_1(), Or_R_2()) => false
  case (Or_R_2(), And_L_1()) => false
  case (And_L_1(), Or_R_1()) => false
  case (Or_R_1(), And_L_1()) => false
  case (And_L_1(), Or_L()) => false
  case (Or_L(), And_L_1()) => false
  case (And_L_1(), Not_R()) => false
  case (Not_R(), And_L_1()) => false
  case (And_L_1(), Not_L()) => false
  case (Not_L(), And_L_1()) => false
  case (And_L_1(), ImpR_R()) => false
  case (ImpR_R(), And_L_1()) => false
  case (And_L_1(), ImpR_L()) => false
  case (ImpR_L(), And_L_1()) => false
  case (And_L_1(), And_R()) => false
  case (And_R(), And_L_1()) => false
  case (And_L_1(), And_L_2()) => false
  case (And_L_2(), And_L_1()) => false
  case (Or_R_2(), Or_R_2()) => true
  case (Or_R_1(), Or_R_1()) => true
  case (Or_L(), Or_L()) => true
  case (Not_R(), Not_R()) => true
  case (Not_L(), Not_L()) => true
  case (ImpR_R(), ImpR_R()) => true
  case (ImpR_L(), ImpR_L()) => true
  case (And_R(), And_R()) => true
  case (And_L_2(), And_L_2()) => true
  case (And_L_1(), And_L_1()) => true
}

abstract sealed class Prooftree
final case class Prooftreea(a: Sequent, b: Rule, c: List[Prooftree]) extends
  Prooftree

abstract sealed class Rule
final case class RuleCuta(a: RuleCut) extends Rule
final case class RuleLa(a: RuleL) extends Rule
final case class RuleStructa(a: RuleStruct) extends Rule
final case class RuleZera(a: RuleZer) extends Rule
final case class RuleMacro(a: List[Char], b: Prooftree) extends Rule
final case class Fail() extends Rule

def equal_Rule(x0: Rule, x1: Rule): Boolean = (x0, x1) match {
  case (RuleMacro(x51, x52), Fail()) => false
  case (Fail(), RuleMacro(x51, x52)) => false
  case (RuleZera(x4), Fail()) => false
  case (Fail(), RuleZera(x4)) => false
  case (RuleZera(x4), RuleMacro(x51, x52)) => false
  case (RuleMacro(x51, x52), RuleZera(x4)) => false
  case (RuleStructa(x3), Fail()) => false
  case (Fail(), RuleStructa(x3)) => false
  case (RuleStructa(x3), RuleMacro(x51, x52)) => false
  case (RuleMacro(x51, x52), RuleStructa(x3)) => false
  case (RuleStructa(x3), RuleZera(x4)) => false
  case (RuleZera(x4), RuleStructa(x3)) => false
  case (RuleLa(x2), Fail()) => false
  case (Fail(), RuleLa(x2)) => false
  case (RuleLa(x2), RuleMacro(x51, x52)) => false
  case (RuleMacro(x51, x52), RuleLa(x2)) => false
  case (RuleLa(x2), RuleZera(x4)) => false
  case (RuleZera(x4), RuleLa(x2)) => false
  case (RuleLa(x2), RuleStructa(x3)) => false
  case (RuleStructa(x3), RuleLa(x2)) => false
  case (RuleCuta(x1), Fail()) => false
  case (Fail(), RuleCuta(x1)) => false
  case (RuleCuta(x1), RuleMacro(x51, x52)) => false
  case (RuleMacro(x51, x52), RuleCuta(x1)) => false
  case (RuleCuta(x1), RuleZera(x4)) => false
  case (RuleZera(x4), RuleCuta(x1)) => false
  case (RuleCuta(x1), RuleStructa(x3)) => false
  case (RuleStructa(x3), RuleCuta(x1)) => false
  case (RuleCuta(x1), RuleLa(x2)) => false
  case (RuleLa(x2), RuleCuta(x1)) => false
  case (RuleMacro(x51, x52), RuleMacro(y51, y52)) =>
    equal_lista[Char](x51, y51) && equal_Prooftreea(x52, y52)
  case (RuleZera(x4), RuleZera(y4)) => equal_RuleZer(x4, y4)
  case (RuleStructa(x3), RuleStructa(y3)) => equal_RuleStruct(x3, y3)
  case (RuleLa(x2), RuleLa(y2)) => equal_RuleL(x2, y2)
  case (RuleCuta(x1), RuleCuta(y1)) => equal_RuleCut(x1, y1)
  case (Fail(), Fail()) => true
}

def equal_Prooftreea(x0: Prooftree, x1: Prooftree): Boolean = (x0, x1) match {
  case (Prooftreea(x1, x2, x3), Prooftreea(y1, y2, y3)) =>
    equal_Sequenta(x1, y1) &&
      (equal_Rule(x2, y2) && equal_lista[Prooftree](x3, y3))
}

implicit def equal_Prooftree: equal[Prooftree] = new equal[Prooftree] {
  val `SequentCalc.equal` = (a: Prooftree, b: Prooftree) =>
    equal_Prooftreea(a, b)
}

implicit def equal_Atprop: equal[Atprop] = new equal[Atprop] {
  val `SequentCalc.equal` = (a: Atprop, b: Atprop) => equal_Atpropa(a, b)
}

implicit def equal_Formula: equal[Formula] = new equal[Formula] {
  val `SequentCalc.equal` = (a: Formula, b: Formula) => equal_Formulaa(a, b)
}

implicit def equal_Sequent: equal[Sequent] = new equal[Sequent] {
  val `SequentCalc.equal` = (a: Sequent, b: Sequent) => equal_Sequenta(a, b)
}

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]
final case class coset[A](a: List[A]) extends set[A]

def bot_set[A]: set[A] = seta[A](Nil)

def removeAll[A : equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def membera[A : equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || membera[A](xs, y)
}

def inserta[A : equal](x: A, xs: List[A]): List[A] =
  (if (membera[A](xs, x)) xs else x :: xs)

def insert[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](removeAll[A](x, xs))
  case (x, seta(xs)) => seta[A](inserta[A](x, xs))
}

def freevars_Atprop(x0: Atprop): set[Atprop] = x0 match {
  case Atprop_Freevar(vara) =>
    insert[Atprop](Atprop_Freevar(vara), bot_set[Atprop])
  case Atpropa(uu) => bot_set[Atprop]
}

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def member[A : equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, coset(xs)) => ! (membera[A](xs, x))
  case (x, seta(xs)) => membera[A](xs, x)
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def sup_set[A : equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (coset(xs), a) => coset[A](filter[A]((x: A) => ! (member[A](x, a)), xs))
  case (seta(xs), a) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => insert[A](aa, b), xs, a)
}

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](map[A, B](f, xs))
}

def freevars_Formula(x0: Formula): set[Formula] = x0 match {
  case Formula_Atprop(vara) =>
    image[Atprop,
           Formula]((a: Atprop) => Formula_Atprop(a), freevars_Atprop(vara))
  case Formula_Bin(var1, uu, var2) =>
    sup_set[Formula](freevars_Formula(var1), freevars_Formula(var2))
  case Formula_Un(uv, vara) => freevars_Formula(vara)
  case Formula_Freevar(vara) =>
    insert[Formula](Formula_Freevar(vara), bot_set[Formula])
}

implicit def equal_Structure: equal[Structure] = new equal[Structure] {
  val `SequentCalc.equal` = (a: Structure, b: Structure) =>
    equal_Structurea(a, b)
}

def freevars_Structure(x0: Structure): set[Structure] = x0 match {
  case Structure_Formula(vara) =>
    image[Formula,
           Structure]((a: Formula) => Structure_Formula(a),
                       freevars_Formula(vara))
  case Structure_Bin(var1, uu, var2) =>
    sup_set[Structure](freevars_Structure(var1), freevars_Structure(var2))
  case Structure_Freevar(vara) =>
    insert[Structure](Structure_Freevar(vara), bot_set[Structure])
  case Structure_Zer(uv) => bot_set[Structure]
}

def freevars_Sequent(x0: Sequent): set[Sequent] = x0 match {
  case Sequenta(var1, var2) =>
    image[Structure,
           Sequent]((a: Structure) => Sequent_Structure(a),
                     sup_set[Structure](freevars_Structure(var1),
 freevars_Structure(var2)))
  case Sequent_Structure(v) => bot_set[Sequent]
}

def replace_Atprop_aux(xa0: Atprop, mtch: Atprop, x: Atprop): Atprop =
  (xa0, mtch, x) match {
  case (Atprop_Freevar(a), mtch, x) =>
    (x match {
       case Atpropa(_) => x
       case Atprop_Freevar(free) =>
         (if (equal_lista[Char](a, free)) mtch else Atprop_Freevar(free))
     })
  case (Atpropa(a), mtch, x) => x
}

def replace_Atprop(x0: (Atprop, Atprop), c: Atprop): Atprop = (x0, c) match {
  case ((a, b), c) => replace_Atprop_aux(a, b, c)
}

def replace_Formula_aux(x: Formula, mtch: Formula, xa2: Formula): Formula =
  (x, mtch, xa2) match {
  case (x, mtch, Formula_Atprop(a)) =>
    (x match {
       case Formula_Atprop(xa) =>
         (mtch match {
            case Formula_Atprop(mtcha) =>
              Formula_Atprop(replace_Atprop((xa, mtcha), a))
            case Formula_Bin(_, _, _) => Formula_Atprop(a)
            case Formula_Freevar(_) => Formula_Atprop(a)
            case Formula_Un(_, _) => Formula_Atprop(a)
          })
       case Formula_Bin(_, _, _) => Formula_Atprop(a)
       case Formula_Freevar(_) => Formula_Atprop(a)
       case Formula_Un(_, _) => Formula_Atprop(a)
     })
  case (x, mtch, Formula_Bin(var1, op1, var2)) =>
    Formula_Bin(replace_Formula_aux(x, mtch, var1), op1,
                 replace_Formula_aux(x, mtch, var2))
  case (x, mtch, Formula_Un(op1, vara)) =>
    Formula_Un(op1, replace_Formula_aux(x, mtch, vara))
  case (x, mtch, Formula_Freevar(free)) =>
    (if (equal_Formulaa(x, Formula_Freevar(free))) mtch
      else Formula_Freevar(free))
}

def replace_Formula(x0: (Formula, Formula), c: Formula): Formula = (x0, c) match
  {
  case ((a, b), c) => replace_Formula_aux(a, b, c)
}

def replace_Structure_aux(x: Structure, mtch: Structure, xa2: Structure):
      Structure
  =
  (x, mtch, xa2) match {
  case (x, mtch, Structure_Formula(f)) =>
    (x match {
       case Structure_Bin(_, _, _) => Structure_Formula(f)
       case Structure_Formula(xf) =>
         (mtch match {
            case Structure_Bin(_, _, _) => Structure_Formula(f)
            case Structure_Formula(mtchf) =>
              Structure_Formula(replace_Formula((xf, mtchf), f))
            case Structure_Freevar(_) => Structure_Formula(f)
            case Structure_Zer(_) => Structure_Formula(f)
          })
       case Structure_Freevar(_) => Structure_Formula(f)
       case Structure_Zer(_) => Structure_Formula(f)
     })
  case (x, mtch, Structure_Bin(var1, op1, var2)) =>
    Structure_Bin(replace_Structure_aux(x, mtch, var1), op1,
                   replace_Structure_aux(x, mtch, var2))
  case (x, mtch, Structure_Freevar(free)) =>
    (if (equal_Structurea(x, Structure_Freevar(free))) mtch
      else Structure_Freevar(free))
  case (x, mtch, Structure_Zer(z)) => Structure_Zer(z)
}

def replace_Structure(x0: (Structure, Structure), c: Structure): Structure =
  (x0, c) match {
  case ((a, b), c) => replace_Structure_aux(a, b, c)
}

def replace_Sequent(x0: (Sequent, Sequent), y: Sequent): Sequent = (x0, y) match
  {
  case ((Sequent_Structure(x), Sequent_Structure(rep)), Sequenta(var1, var2)) =>
    Sequenta(replace_Structure((x, rep), var1),
              replace_Structure((x, rep), var2))
  case ((Sequenta(v, va), uv), y) => y
  case ((uu, Sequenta(v, va)), y) => y
  case ((uu, uv), Sequent_Structure(v)) => Sequent_Structure(v)
}

def match_Atprop(xa0: Atprop, x: Atprop): List[(Atprop, Atprop)] = (xa0, x)
  match {
  case (Atprop_Freevar(free), x) => List((Atprop_Freevar(free), x))
  case (Atpropa(uu), uv) => Nil
}

def snda[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def fsta[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def list_ex[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => false
  case (p, x :: xs) => p(x) || list_ex[A](p, xs)
}

def m_clash[A : equal, B : equal](x: (A, B), y: List[(A, B)]): Boolean =
  list_ex[(A, B)]((a: (A, B)) =>
                    eq[A](fsta[A, B](a), fsta[A, B](x)) &&
                      ! (eq[B](snda[A, B](a), snda[A, B](x))),
                   y)

def merge[A : equal, B : equal](x0: List[(A, B)], y: List[(A, B)]): List[(A, B)]
  =
  (x0, y) match {
  case (Nil, y) => y
  case (x :: xs, y) =>
    (if (m_clash[A, B](x, y))
      merge[A, B](filter[(A, B)]((a: (A, B)) =>
                                   ! (eq[A](fsta[A, B](a), fsta[A, B](x))),
                                  xs),
                   filter[(A, B)]((a: (A, B)) =>
                                    ! (eq[A](fsta[A, B](a), fsta[A, B](x))),
                                   y))
      else x :: merge[A, B](xs, y))
}

def match_Formula(xa0: Formula, x: Formula): List[(Formula, Formula)] = (xa0, x)
  match {
  case (Formula_Atprop(rule), x) =>
    (x match {
       case Formula_Atprop(m) =>
         map[(Atprop, Atprop),
              (Formula,
                Formula)]((a: (Atprop, Atprop)) =>
                            {
                              val (xa, y): (Atprop, Atprop) = a;
                              (Formula_Atprop(xa), Formula_Atprop(y))
                            },
                           match_Atprop(rule, m))
       case Formula_Bin(_, _, _) => Nil
       case Formula_Freevar(_) => Nil
       case Formula_Un(_, _) => Nil
     })
  case (Formula_Bin(var11, op1, var12), x) =>
    (x match {
       case Formula_Atprop(_) => Nil
       case Formula_Bin(var21, op2, var22) =>
         (if (equal_Formula_Bin_Op(op1, op2))
           merge[Formula,
                  Formula](match_Formula(var11, var21),
                            match_Formula(var12, var22))
           else Nil)
       case Formula_Freevar(_) => Nil
       case Formula_Un(_, _) => Nil
     })
  case (Formula_Un(op1, var1), x) =>
    (x match {
       case Formula_Atprop(_) => Nil
       case Formula_Bin(_, _, _) => Nil
       case Formula_Freevar(_) => Nil
       case Formula_Un(op2, var2) =>
         (if (equal_Formula_Un_Op(op1, op2)) match_Formula(var1, var2) else Nil)
     })
  case (Formula_Freevar(free), x) => List((Formula_Freevar(free), x))
}

def match_Structure(xa0: Structure, x: Structure): List[(Structure, Structure)]
  =
  (xa0, x) match {
  case (Structure_Formula(rule), x) =>
    (x match {
       case Structure_Bin(_, _, _) => Nil
       case Structure_Formula(form) =>
         map[(Formula, Formula),
              (Structure,
                Structure)]((a: (Formula, Formula)) =>
                              {
                                val (xa, y): (Formula, Formula) = a;
                                (Structure_Formula(xa), Structure_Formula(y))
                              },
                             match_Formula(rule, form))
       case Structure_Freevar(_) => Nil
       case Structure_Zer(_) => Nil
     })
  case (Structure_Bin(var11, op1, var12), x) =>
    (x match {
       case Structure_Bin(var21, op2, var22) =>
         (if (equal_Structure_Bin_Op(op1, op2))
           merge[Structure,
                  Structure](match_Structure(var11, var21),
                              match_Structure(var12, var22))
           else Nil)
       case Structure_Formula(_) => Nil
       case Structure_Freevar(_) => Nil
       case Structure_Zer(_) => Nil
     })
  case (Structure_Freevar(free), x) => List((Structure_Freevar(free), x))
  case (Structure_Zer(uu), x) => Nil
}

def match_Sequent(uu: Sequent, uv: Sequent): List[(Sequent, Sequent)] = (uu, uv)
  match {
  case (Sequenta(var11, var12), Sequenta(var21, var22)) =>
    map[(Structure, Structure),
         (Sequent,
           Sequent)]((a: (Structure, Structure)) =>
                       {
                         val (x, y): (Structure, Structure) = a;
                         (Sequent_Structure(x), Sequent_Structure(y))
                       },
                      merge[Structure,
                             Structure](match_Structure(var11, var21),
 match_Structure(var12, var22)))
  case (Sequent_Structure(v), uv) => Nil
  case (uu, Sequent_Structure(v)) => Nil
}

trait Varmatch[A] {
  val `SequentCalc.matcha`: (A, A) => List[(A, A)]
  val `SequentCalc.freevars`: A => set[A]
  val `SequentCalc.replace`: ((A, A), A) => A
}
def matcha[A](a: A, b: A)(implicit A: Varmatch[A]): List[(A, A)] =
  A.`SequentCalc.matcha`(a, b)
def freevars[A](a: A)(implicit A: Varmatch[A]): set[A] =
  A.`SequentCalc.freevars`(a)
def replace[A](a: (A, A), b: A)(implicit A: Varmatch[A]): A =
  A.`SequentCalc.replace`(a, b)

implicit def Varmatch_Sequent: Varmatch[Sequent] = new Varmatch[Sequent] {
  val `SequentCalc.matcha` = (a: Sequent, b: Sequent) => match_Sequent(a, b)
  val `SequentCalc.freevars` = (a: Sequent) => freevars_Sequent(a)
  val `SequentCalc.replace` = (a: (Sequent, Sequent), b: Sequent) =>
    replace_Sequent(a, b)
}

abstract sealed class nibble
final case class Nibble0() extends nibble
final case class Nibble1() extends nibble
final case class Nibble2() extends nibble
final case class Nibble3() extends nibble
final case class Nibble4() extends nibble
final case class Nibble5() extends nibble
final case class Nibble6() extends nibble
final case class Nibble7() extends nibble
final case class Nibble8() extends nibble
final case class Nibble9() extends nibble
final case class NibbleA() extends nibble
final case class NibbleB() extends nibble
final case class NibbleC() extends nibble
final case class NibbleD() extends nibble
final case class NibbleE() extends nibble
final case class NibbleF() extends nibble

abstract sealed class multiset[A]
final case class multiset_of[A](a: List[A]) extends multiset[A]

abstract sealed class Locale
final case class CutFormula(a: Formula) extends Locale
final case class Premise(a: Sequent) extends Locale
final case class Part(a: Structure) extends Locale
final case class Empty() extends Locale

abstract sealed class ruleder
final case class ruledera(a: Sequent, b: Sequent => Option[List[Sequent]])
  extends ruleder
final case class
  ruleder_cond(a: Sequent => Boolean, b: Sequent,
                c: Sequent => Option[List[Sequent]])
  extends ruleder

abstract sealed class polarity
final case class Plus() extends polarity
final case class Minus() extends polarity
final case class N() extends polarity

def id[A]: A => A = (x: A) => x

def comp[A, B, C](f: A => B, g: C => A): C => B = (x: C) => f(g(x))

def nulla[A](x0: List[A]): Boolean = x0 match {
  case Nil => true
  case x :: xs => false
}

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def extract[A](p: A => Boolean, x1: List[A]): Option[(List[A], (A, List[A]))] =
  (p, x1) match {
  case (p, x :: xs) =>
    (if (p(x)) Some[(List[A], (A, List[A]))]((Nil, (x, xs)))
      else (extract[A](p, xs) match {
              case None => None
              case Some((ys, (y, zs))) =>
                Some[(List[A], (A, List[A]))]((x :: ys, (y, zs)))
            }))
  case (p, Nil) => None
}

def is_empty[A](x0: set[A]): Boolean = x0 match {
  case seta(xs) => nulla[A](xs)
}

def pred_list[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && pred_list[A](p, xs)
}

def ant(x0: Sequent): Structure = x0 match {
  case Sequenta(x, y) => x
  case Sequent_Structure(x) => x
}

def replaceAll[A : Varmatch](x0: List[(A, A)], mtch: A): A = (x0, mtch) match {
  case (Nil, mtch) => mtch
  case (x :: xs, mtch) => replaceAll[A](xs, replace[A](x, mtch))
}

def ruleMatch[A : equal : Varmatch](r: A, m: A): Boolean =
  (if (is_empty[A](freevars[A](m))) eq[A](replaceAll[A](matcha[A](r, m), r), m)
    else false)

def ruleRuleStruct(x: Locale, xa1: RuleStruct): ruleder = (x, xa1) match {
  case (x, W_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Formula(Formula_Freevar(List('A')))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Y'))))))
  case (x, P_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Bin(Structure_Freevar(List('X',
                                  '1')),
           Structure_Comma(), Structure_Freevar(List('B'))),
                                     Structure_Comma(),
                                     Structure_Bin(Structure_Freevar(List('A')),
            Structure_Comma(), Structure_Freevar(List('X', '2')))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Bin(Structure_Freevar(List('X',
                      '1')),
                                       Structure_Comma(),
                                       Structure_Freevar(List('A'))),
                         Structure_Comma(),
                         Structure_Bin(Structure_Freevar(List('B')),
Structure_Comma(), Structure_Freevar(List('X', '2')))),
           Structure_Freevar(List('Y'))))))
  case (x, I_R_R2()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Bin(Structure_Freevar(List('Y')),
                                      Structure_Comma(),
                                      Structure_Zer(Structure_Empty()))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Y'))))))
  case (x, A_R2()) =>
    ruledera(Sequenta(Structure_Freevar(List('W')),
                       Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
            Structure_Comma(), Structure_Freevar(List('Y'))),
                                      Structure_Comma(),
                                      Structure_Freevar(List('Z')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('W')),
           Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                          Structure_Bin(Structure_Freevar(List('Y')),
 Structure_Comma(), Structure_Freevar(List('Z'))))))))
  case (x, A_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('W')),
                       Structure_Bin(Structure_Freevar(List('X')),
                                      Structure_Comma(),
                                      Structure_Bin(Structure_Freevar(List('Y')),
             Structure_Comma(), Structure_Freevar(List('Z'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('W')),
           Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
Structure_Comma(), Structure_Freevar(List('Y'))),
                          Structure_Comma(), Structure_Freevar(List('Z')))))))
  case (x, I_R_L()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Zer(Structure_Empty()), Structure_Comma(),
                          Structure_Freevar(List('Y')))))))
  case (x, I_L_L2()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Zer(Structure_Empty()),
                                     Structure_Comma(),
                                     Structure_Freevar(List('X'))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Y'))))))
  case (x, I_L_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_Comma(), Structure_Zer(Structure_Empty())),
           Structure_Freevar(List('Y'))))))
  case (x, C_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Formula(Formula_Freevar(List('A')))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_Comma(),
                         Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
Structure_Comma(), Structure_Formula(Formula_Freevar(List('A'))))),
           Structure_Freevar(List('Y'))))))
  case (x, C_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
                                      Structure_Comma(),
                                      Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
Structure_Comma(), Structure_Formula(Formula_Freevar(List('A')))),
                          Structure_Comma(), Structure_Freevar(List('Y')))))))
  case (x, I_L_L()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Zer(Structure_Empty()),
                         Structure_Comma(), Structure_Freevar(List('X'))),
           Structure_Freevar(List('Y'))))))
  case (x, I_R_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Freevar(List('Y')), Structure_Comma(),
                          Structure_Zer(Structure_Empty()))))))
  case (x, I_L_R2()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Zer(Structure_Empty())),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Y'))))))
  case (x, A_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Bin(Structure_Freevar(List('Y')),
            Structure_Comma(), Structure_Freevar(List('Z')))),
                       Structure_Freevar(List('W'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
                                       Structure_Comma(),
                                       Structure_Freevar(List('Y'))),
                         Structure_Comma(), Structure_Freevar(List('Z'))),
           Structure_Freevar(List('W'))))))
  case (x, P_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Bin(Structure_Bin(Structure_Freevar(List('Y',
                                   '1')),
            Structure_Comma(), Structure_Freevar(List('B'))),
                                      Structure_Comma(),
                                      Structure_Bin(Structure_Freevar(List('A')),
             Structure_Comma(), Structure_Freevar(List('Y', '2'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Bin(Structure_Freevar(List('Y', '1')),
Structure_Comma(), Structure_Freevar(List('A'))),
                          Structure_Comma(),
                          Structure_Bin(Structure_Freevar(List('B')),
 Structure_Comma(), Structure_Freevar(List('Y', '2'))))))))
  case (x, I_R_L2()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Bin(Structure_Zer(Structure_Empty()),
                                      Structure_Comma(),
                                      Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Y'))))))
  case (x, A_L2()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
           Structure_Comma(), Structure_Freevar(List('Y'))),
                                     Structure_Comma(),
                                     Structure_Freevar(List('Z'))),
                       Structure_Freevar(List('W'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_Comma(),
                         Structure_Bin(Structure_Freevar(List('Y')),
Structure_Comma(), Structure_Freevar(List('Z')))),
           Structure_Freevar(List('W'))))))
  case (x, W_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
                                      Structure_Comma(),
                                      Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Y'))))))
}

def ruleRuleZer(x: Locale, xa1: RuleZer): ruleder = (x, xa1) match {
  case (x, Prem()) =>
    (x match {
       case CutFormula(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Premise(seq) =>
         ruleder_cond((a: Sequent) => equal_Sequenta(seq, a),
                       Sequenta(Structure_Freevar(List('X')),
                                 Structure_Freevar(List('Y'))),
                       (_: Sequent) => Some[List[Sequent]](Nil))
       case Part(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
  case (x, Partial()) =>
    (x match {
       case CutFormula(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Premise(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Part(struct) =>
         ruleder_cond((a: Sequent) =>
                        {
                          val (Sequenta(lhs, rhs)): Sequent = a;
                          equal_Structurea(struct, lhs) ||
                            equal_Structurea(struct, rhs)
                        },
                       Sequenta(Structure_Freevar(List('X')),
                                 Structure_Freevar(List('Y'))),
                       (_: Sequent) => Some[List[Sequent]](Nil))
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
  case (x, Id()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Freevar(List('f'))),
                       Structure_Formula(Formula_Freevar(List('f')))),
              (_: Sequent) => Some[List[Sequent]](Nil))
}

def ruleRuleCut(x: Locale, xa1: RuleCut): ruleder = (x, xa1) match {
  case (x, SingleCut()) =>
    (x match {
       case CutFormula(f) =>
         ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
  Structure_Comma(), Structure_Freevar(List('W'))),
                            Structure_Bin(Structure_Freevar(List('Z')),
   Structure_Comma(), Structure_Freevar(List('Y')))),
                   (_: Sequent) =>
                     Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
                Structure_Bin(Structure_Freevar(List('Z')), Structure_Comma(),
                               Structure_Formula(f))),
       Sequenta(Structure_Bin(Structure_Formula(f), Structure_Comma(),
                               Structure_Freevar(List('W'))),
                 Structure_Freevar(List('Y'))))))
       case Premise(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Part(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
}

def ruleRuleL(x: Locale, xa1: RuleL): ruleder = (x, xa1) match {
  case (x, Not_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Formula(Formula_Un(Formula_Not(),
                           Formula_Freevar(List('A'))))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
                          Structure_Comma(), Structure_Freevar(List('Y')))))))
  case (x, And_L_1()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
                            Formula_And(), Formula_Freevar(List('B'))))),
                       Structure_Freevar(List('Z'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_Comma(),
                         Structure_Formula(Formula_Freevar(List('A')))),
           Structure_Freevar(List('Z'))))))
  case (x, And_L_2()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
                            Formula_And(), Formula_Freevar(List('B'))))),
                       Structure_Freevar(List('Z'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_Comma(),
                         Structure_Formula(Formula_Freevar(List('B')))),
           Structure_Freevar(List('Z'))))))
  case (x, ImpR_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Bin(Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
                            Formula_ImpR(), Formula_Freevar(List('B')))),
                                      Structure_Comma(),
                                      Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('Z')),
                         Structure_Comma(),
                         Structure_Formula(Formula_Freevar(List('A')))),
           Structure_Bin(Structure_Formula(Formula_Freevar(List('B'))),
                          Structure_Comma(), Structure_Freevar(List('X')))))))
  case (x, Or_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
           Structure_Comma(), Structure_Freevar(List('Z'))),
                                     Structure_Comma(),
                                     Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
                            Formula_Or(), Formula_Freevar(List('B'))))),
                       Structure_Bin(Structure_Freevar(List('Y')),
                                      Structure_Comma(),
                                      Structure_Freevar(List('W')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_Comma(),
                         Structure_Formula(Formula_Freevar(List('A')))),
           Structure_Freevar(List('Y'))),
  Sequenta(Structure_Bin(Structure_Freevar(List('Z')), Structure_Comma(),
                          Structure_Formula(Formula_Freevar(List('B')))),
            Structure_Freevar(List('W'))))))
  case (x, Not_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Bin(Structure_Formula(Formula_Un(Formula_Not(),
                           Formula_Freevar(List('A')))),
                                      Structure_Comma(),
                                      Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_Comma(),
                         Structure_Formula(Formula_Freevar(List('A')))),
           Structure_Freevar(List('Y'))))))
  case (x, ImpR_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
           Structure_Comma(), Structure_Freevar(List('Z'))),
                                     Structure_Comma(),
                                     Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
                            Formula_ImpR(), Formula_Freevar(List('B'))))),
                       Structure_Bin(Structure_Freevar(List('Y')),
                                      Structure_Comma(),
                                      Structure_Freevar(List('W')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
                          Structure_Comma(), Structure_Freevar(List('Y')))),
  Sequenta(Structure_Bin(Structure_Freevar(List('Z')), Structure_Comma(),
                          Structure_Formula(Formula_Freevar(List('B')))),
            Structure_Freevar(List('W'))))))
  case (x, And_R()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Freevar(List('Z'))),
                       Structure_Bin(Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
                            Formula_And(), Formula_Freevar(List('B')))),
                                      Structure_Comma(),
                                      Structure_Bin(Structure_Freevar(List('Y')),
             Structure_Comma(), Structure_Freevar(List('W'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
                          Structure_Comma(), Structure_Freevar(List('Y')))),
  Sequenta(Structure_Freevar(List('Z')),
            Structure_Bin(Structure_Formula(Formula_Freevar(List('B'))),
                           Structure_Comma(), Structure_Freevar(List('W')))))))
  case (x, Or_R_2()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Bin(Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
                            Formula_Or(), Formula_Freevar(List('B')))),
                                      Structure_Comma(),
                                      Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Z')),
           Structure_Bin(Structure_Formula(Formula_Freevar(List('B'))),
                          Structure_Comma(), Structure_Freevar(List('X')))))))
  case (x, Or_R_1()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Bin(Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
                            Formula_Or(), Formula_Freevar(List('B')))),
                                      Structure_Comma(),
                                      Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Z')),
           Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
                          Structure_Comma(), Structure_Freevar(List('X')))))))
}

def rule(l: Locale, x1: Rule): ruleder = (l, x1) match {
  case (l, RuleCuta(r)) => ruleRuleCut(l, r)
  case (l, RuleLa(r)) => ruleRuleL(l, r)
  case (l, RuleStructa(r)) => ruleRuleStruct(l, r)
  case (l, RuleZera(r)) => ruleRuleZer(l, r)
  case (uu, RuleMacro(v, va)) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) => None)
  case (uu, Fail()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) => None)
}

def cond(x0: ruleder): Option[Sequent => Boolean] = x0 match {
  case ruleder_cond(c, va, vb) => Some[Sequent => Boolean](c)
  case ruledera(vc, vd) => None
}

def snd(x0: ruleder): Sequent => Option[List[Sequent]] = x0 match {
  case ruledera(ux, y) => y
  case ruleder_cond(uy, uz, y) => y
}

def fst(x0: ruleder): Sequent = x0 match {
  case ruledera(x, uu) => x
  case ruleder_cond(uv, x, uw) => x
}

def der(l: Locale, r: Rule, s: Sequent): (Rule, List[Sequent]) =
  ((snd(rule(l, r))).apply(s) match {
     case None => (Fail(), Nil)
     case Some(conclusion) =>
       (if (ruleMatch[Sequent](fst(rule(l, r)), s))
         (cond(rule(l, r)) match {
            case None =>
              (r, map[Sequent,
                       Sequent]((a: Sequent) =>
                                  replaceAll[Sequent](match_Sequent(fst(rule(l,
                                      r)),
                             s),
               a),
                                 conclusion))
            case Some(condition) =>
              (if (condition(s))
                (r, map[Sequent,
                         Sequent]((a: Sequent) =>
                                    replaceAll[Sequent](match_Sequent(fst(rule(l,
r)),
                               s),
                 a),
                                   conclusion))
                else (Fail(), Nil))
          })
         else (Fail(), Nil))
   })

def concl(x0: Prooftree): Sequent = x0 match {
  case Prooftreea(a, b, c) => a
}

def consq(x0: Sequent): Structure = x0 match {
  case Sequenta(x, y) => y
  case Sequent_Structure(x) => x
}

def ruleList: List[Rule] =
  map[RuleCut, Rule]((a: RuleCut) => RuleCuta(a), List(SingleCut())) ++
    (map[RuleL,
          Rule]((a: RuleL) => RuleLa(a),
                 List(Not_L(), And_L_1(), And_L_2(), ImpR_R(), Or_L(), Not_R(),
                       ImpR_L(), And_R(), Or_R_2(), Or_R_1())) ++
      (map[RuleStruct,
            Rule]((a: RuleStruct) => RuleStructa(a),
                   List(W_L(), P_L(), I_R_R2(), A_R2(), A_R(), I_R_L(),
                         I_L_L2(), I_L_R(), C_L(), C_R(), I_L_L(), I_R_R(),
                         I_L_R2(), A_L(), P_R(), I_R_L2(), A_L2(), W_R())) ++
        map[RuleZer,
             Rule]((a: RuleZer) => RuleZera(a), List(Prem(), Partial(), Id()))))

def fresh_name_aux(x0: List[List[Char]], s: List[Char], uu: set[List[Char]]):
      List[Char]
  =
  (x0, s, uu) match {
  case (Nil, s, uu) => s
  case (x :: xs, s, full) =>
    (if (! (member[List[Char]](s ++ x, full))) s ++ x
      else fresh_name_aux(xs, s ++ x, full))
}

def fresh_name(list: List[List[Char]]): List[Char] =
  fresh_name_aux(list, List('X'), seta[List[Char]](list))

def ms_lesseq_impl[A : equal](x0: List[A], ys: List[A]): Option[Boolean] =
  (x0, ys) match {
  case (Nil, ys) => Some[Boolean](! (nulla[A](ys)))
  case (x :: xs, ys) =>
    (extract[A]((a: A) => eq[A](x, a), ys) match {
       case None => None
       case Some((ys1, (_, ys2))) => ms_lesseq_impl[A](xs, ys1 ++ ys2)
     })
}

def collectPremises(x0: Prooftree): List[Sequent] = x0 match {
  case Prooftreea(p, RuleZera(Prem()), Nil) => List(p)
  case Prooftreea(uu, RuleMacro(uv, pt), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleCuta(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleLa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleStructa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleZera(Id()), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleZera(Partial()), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, Fail(), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleZera(vb), v :: va) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            v :: va)).apply(Nil)
}

def collectPremisesToLocale(pt: Prooftree): List[Locale] =
  map[Sequent, Locale]((a: Sequent) => Premise(a), collectPremises(pt))

def less_eq_set[A : equal](a: set[A], b: set[A]): Boolean = (a, b) match {
  case (coset(Nil), seta(Nil)) => false
  case (a, coset(ys)) => pred_list[A]((y: A) => ! (member[A](y, a)), ys)
  case (seta(xs), b) => pred_list[A]((x: A) => member[A](x, b), xs)
}

def equal_set[A : equal](a: set[A], b: set[A]): Boolean =
  less_eq_set[A](a, b) && less_eq_set[A](b, a)

def isProofTree(loc: List[Locale], x1: Prooftree): Boolean = (loc, x1) match {
  case (loc, Prooftreea(s, RuleMacro(n, pt), ptlist)) =>
    equal_Sequenta(s, concl(pt)) &&
      (isProofTree(loc ++ collectPremisesToLocale(pt), pt) &&
        (equal_set[Sequent](seta[Sequent](collectPremises(pt)),
                             seta[Sequent](map[Prooftree,
        Sequent]((a: Prooftree) => concl(a), ptlist))) &&
          (foldr[Prooftree,
                  Boolean](comp[Boolean, Boolean => Boolean,
                                 Prooftree]((a: Boolean) =>
      (b: Boolean) => a && b,
     (a: Prooftree) => isProofTree(loc, a)),
                            ptlist)).apply(true)))
  case (loc, Prooftreea(s, RuleCuta(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleCuta(v), s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleCuta(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleLa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleLa(v), s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleLa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleStructa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleStructa(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleStructa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleZera(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleZera(v), s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleZera(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, Fail(), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule, List[Sequent]](der(x, Fail(), s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, Fail(), s))))),
                        loc)).apply(false)
}

def equal_option[A : equal](x0: Option[A], x1: Option[A]): Boolean = (x0, x1)
  match {
  case (None, Some(x2)) => false
  case (Some(x2), None) => false
  case (Some(x2), Some(y2)) => eq[A](x2, y2)
  case (None, None) => true
}

def equal_multiset[A : equal](x0: multiset[A], x1: multiset[A]): Boolean =
  (x0, x1) match {
  case (multiset_of(xs), multiset_of(ys)) =>
    equal_option[Boolean](ms_lesseq_impl[A](xs, ys), Some[Boolean](false))
}

def collect_freevars_Structure(x0: Structure): List[Structure] = x0 match {
  case Structure_Formula(f) => List(Structure_Formula(f))
  case Structure_Bin(l, uu, r) =>
    collect_freevars_Structure(l) ++ collect_freevars_Structure(r)
  case Structure_Freevar(free) => List(Structure_Freevar(free))
  case Structure_Zer(z) => List(Structure_Zer(z))
}

def collect_freevars_Sequent(x0: Sequent): List[Structure] = x0 match {
  case Sequenta(l, r) =>
    collect_freevars_Structure(l) ++ collect_freevars_Structure(r)
  case Sequent_Structure(uu) => Nil
}

def is_display_rule(r: Rule): List[Rule] =
  (if (((snd(rule(Empty(), r))).apply(fst(rule(Empty(), r))) match {
          case None => false
          case Some(Nil) => false
          case Some(h :: _) =>
            equal_multiset[Structure](multiset_of[Structure](collect_freevars_Sequent(fst(rule(Empty(),
                r)))),
                                       multiset_of[Structure](collect_freevars_Sequent(h)))
        }))
    List(r) else Nil)

def displayRules: List[Rule] =
  (foldr[Rule,
          List[Rule]](comp[List[Rule], (List[Rule]) => List[Rule],
                            Rule]((a: List[Rule]) => (b: List[Rule]) => a ++ b,
                                   (a: Rule) => is_display_rule(a)),
                       ruleList)).apply(Nil)

def structure_Op_polarity(x0: Structure_Bin_Op): (polarity, polarity) = x0 match
  {
  case Structure_Comma() => (Plus(), Plus())
}

def polarity_weird_xor(xa0: polarity, x: polarity): polarity = (xa0, x) match {
  case (Plus(), N()) => Plus()
  case (Minus(), N()) => Minus()
  case (N(), x) => x
  case (Plus(), Plus()) => N()
  case (Plus(), Minus()) => N()
  case (Minus(), Plus()) => N()
  case (Minus(), Minus()) => N()
}

def polarity_not(x0: polarity): polarity = x0 match {
  case Minus() => Plus()
  case Plus() => Minus()
  case N() => N()
}

def polarity_weird_and(xa0: polarity, x: polarity): polarity = (xa0, x) match {
  case (Minus(), x) => polarity_not(x)
  case (Plus(), x) => x
  case (N(), uu) => N()
}

def polarity_Structure(s: Structure, x1: Structure): polarity = (s, x1) match {
  case (s, Structure_Bin(l, oper, r)) =>
    (if (equal_Structurea(l, s))
      fsta[polarity, polarity](structure_Op_polarity(oper))
      else (if (equal_Structurea(r, s))
             snda[polarity, polarity](structure_Op_polarity(oper))
             else polarity_weird_xor(polarity_weird_and(fsta[polarity,
                      polarity](structure_Op_polarity(oper)),
                 polarity_Structure(s, l)),
                                      polarity_weird_and(snda[polarity,
                       polarity](structure_Op_polarity(oper)),
                  polarity_Structure(s, r)))))
  case (s, Structure_Formula(v)) =>
    (if (equal_Structurea(s, Structure_Formula(v))) Plus() else N())
  case (s, Structure_Freevar(v)) =>
    (if (equal_Structurea(s, Structure_Freevar(v))) Plus() else N())
  case (s, Structure_Zer(v)) =>
    (if (equal_Structurea(s, Structure_Zer(v))) Plus() else N())
}

def partial_goal(s: Structure, x1: Structure): Structure = (s, x1) match {
  case (s, Structure_Bin(l, oper, r)) =>
    (polarity_Structure(s, l) match {
       case Plus() => l
       case Minus() => l
       case N() => (if (equal_Structurea(s, l)) l else r)
     })
  case (s, Structure_Formula(v)) => Structure_Formula(v)
  case (s, Structure_Freevar(v)) => Structure_Freevar(v)
  case (s, Structure_Zer(v)) => Structure_Zer(v)
}

def replaceIntoPT_list(list: List[(Sequent, Sequent)], x1: List[Prooftree]):
      List[Prooftree]
  =
  (list, x1) match {
  case (list, Nil) => Nil
  case (list, l :: ist) =>
    replaceIntoPT_aux(list, l) :: replaceIntoPT_list(list, ist)
}

def replaceIntoPT_aux(list: List[(Sequent, Sequent)], x1: Prooftree): Prooftree
  =
  (list, x1) match {
  case (list, Prooftreea(c, RuleMacro(s, pt), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c),
                RuleMacro(s, replaceIntoPT_aux(list, pt)),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleCuta(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleCuta(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleLa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleLa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleStructa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleStructa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleZera(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleZera(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, Fail(), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), Fail(),
                replaceIntoPT_list(list, ptlist))
}

def replaceIntoPT(seq: Sequent, x1: Prooftree): Prooftree = (seq, x1) match {
  case (seq, Prooftreea(c, r, ptlist)) =>
    replaceIntoPT_aux(match_Sequent(c, seq), Prooftreea(c, r, ptlist))
}

def rulifyFormula(x0: Formula): Formula = x0 match {
  case Formula_Atprop(Atpropa(f :: a)) =>
    (if ('A' <= f && f <= 'Z') Formula_Freevar(f :: a)
      else Formula_Atprop(Atprop_Freevar(f :: a)))
  case Formula_Bin(x, c, y) =>
    Formula_Bin(rulifyFormula(x), c, rulifyFormula(y))
  case Formula_Atprop(Atpropa(Nil)) => Formula_Atprop(Atpropa(Nil))
  case Formula_Atprop(Atprop_Freevar(va)) => Formula_Atprop(Atprop_Freevar(va))
  case Formula_Freevar(v) => Formula_Freevar(v)
  case Formula_Un(v, va) => Formula_Un(v, va)
}

def rulifyStructure(x0: Structure): Structure = x0 match {
  case Structure_Formula(Formula_Atprop(Atpropa(f :: a))) =>
    (if ('A' <= f && f <= 'Z')
      (if (f == 'F') Structure_Formula(Formula_Freevar(f :: a))
        else Structure_Freevar(f :: a))
      else Structure_Formula(Formula_Atprop(Atprop_Freevar(f :: a))))
  case Structure_Formula(Formula_Atprop(Atpropa(Nil))) =>
    Structure_Formula(rulifyFormula(Formula_Atprop(Atpropa(Nil))))
  case Structure_Formula(Formula_Atprop(Atprop_Freevar(va))) =>
    Structure_Formula(rulifyFormula(Formula_Atprop(Atprop_Freevar(va))))
  case Structure_Formula(Formula_Bin(v, va, vb)) =>
    Structure_Formula(rulifyFormula(Formula_Bin(v, va, vb)))
  case Structure_Formula(Formula_Freevar(v)) =>
    Structure_Formula(rulifyFormula(Formula_Freevar(v)))
  case Structure_Formula(Formula_Un(v, va)) =>
    Structure_Formula(rulifyFormula(Formula_Un(v, va)))
  case Structure_Bin(x, c, y) =>
    Structure_Bin(rulifyStructure(x), c, rulifyStructure(y))
  case Structure_Freevar(v) => Structure_Freevar(v)
  case Structure_Zer(v) => Structure_Zer(v)
}

def rulifySequent(x0: Sequent): Sequent = x0 match {
  case Sequenta(x, y) => Sequenta(rulifyStructure(x), rulifyStructure(y))
  case Sequent_Structure(x) => Sequent_Structure(x)
}

def replaceIntoProoftree(list: List[Prooftree], x1: Prooftree): Prooftree =
  (list, x1) match {
  case (Nil, Prooftreea(s, RuleZera(Prem()), Nil)) =>
    Prooftreea(s, RuleZera(Prem()), Nil)
  case (l :: ist, Prooftreea(s, RuleZera(Prem()), Nil)) =>
    (if (equal_Sequenta(concl(l), s)) l
      else replaceIntoProoftree(ist, Prooftreea(s, RuleZera(Prem()), Nil)))
  case (v :: va, Prooftreea(s, RuleCuta(vb), Nil)) =>
    Prooftreea(s, RuleCuta(vb), Nil)
  case (v :: va, Prooftreea(s, RuleLa(vb), Nil)) =>
    Prooftreea(s, RuleLa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleStructa(vb), Nil)) =>
    Prooftreea(s, RuleStructa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleZera(Id()), Nil)) =>
    Prooftreea(s, RuleZera(Id()), Nil)
  case (v :: va, Prooftreea(s, RuleZera(Partial()), Nil)) =>
    Prooftreea(s, RuleZera(Partial()), Nil)
  case (v :: va, Prooftreea(s, RuleMacro(vb, vc), Nil)) =>
    Prooftreea(s, RuleMacro(vb, vc), Nil)
  case (v :: va, Prooftreea(s, Fail(), Nil)) => Prooftreea(s, Fail(), Nil)
  case (list, Prooftreea(s, RuleCuta(v), Nil)) =>
    Prooftreea(s, RuleCuta(v), Nil)
  case (list, Prooftreea(s, RuleLa(v), Nil)) => Prooftreea(s, RuleLa(v), Nil)
  case (list, Prooftreea(s, RuleStructa(v), Nil)) =>
    Prooftreea(s, RuleStructa(v), Nil)
  case (list, Prooftreea(s, RuleZera(Id()), Nil)) =>
    Prooftreea(s, RuleZera(Id()), Nil)
  case (list, Prooftreea(s, RuleZera(Partial()), Nil)) =>
    Prooftreea(s, RuleZera(Partial()), Nil)
  case (list, Prooftreea(s, RuleMacro(v, va), Nil)) =>
    Prooftreea(s, RuleMacro(v, va), Nil)
  case (list, Prooftreea(s, Fail(), Nil)) => Prooftreea(s, Fail(), Nil)
  case (v :: va, Prooftreea(s, RuleCuta(vb), vc :: vd)) =>
    Prooftreea(s, RuleCuta(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleLa(vb), vc :: vd)) =>
    Prooftreea(s, RuleLa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleStructa(vb), vc :: vd)) =>
    Prooftreea(s, RuleStructa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleZera(Id()), vb :: vc)) =>
    Prooftreea(s, RuleZera(Id()),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vb :: vc))
  case (v :: va, Prooftreea(s, RuleZera(Partial()), vb :: vc)) =>
    Prooftreea(s, RuleZera(Partial()),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vb :: vc))
  case (v :: va, Prooftreea(s, RuleMacro(vb, vc), vd :: ve)) =>
    Prooftreea(s, RuleMacro(vb, vc),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vd :: ve))
  case (v :: va, Prooftreea(s, Fail(), vb :: vc)) =>
    Prooftreea(s, Fail(),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vb :: vc))
  case (v :: va, Prooftreea(s, r, vb :: vc)) =>
    Prooftreea(s, r,
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vb :: vc))
  case (list, Prooftreea(s, RuleCuta(v), va :: vb)) =>
    Prooftreea(s, RuleCuta(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleLa(v), va :: vb)) =>
    Prooftreea(s, RuleLa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleStructa(v), va :: vb)) =>
    Prooftreea(s, RuleStructa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleZera(Id()), v :: va)) =>
    Prooftreea(s, RuleZera(Id()),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 v :: va))
  case (list, Prooftreea(s, RuleZera(Partial()), v :: va)) =>
    Prooftreea(s, RuleZera(Partial()),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 v :: va))
  case (list, Prooftreea(s, RuleMacro(v, va), vb :: vc)) =>
    Prooftreea(s, RuleMacro(v, va),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 vb :: vc))
  case (list, Prooftreea(s, Fail(), v :: va)) =>
    Prooftreea(s, Fail(),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 v :: va))
  case (list, Prooftreea(s, r, v :: va)) =>
    Prooftreea(s, r,
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 v :: va))
}

def expandProoftree(x0: Prooftree): Prooftree = x0 match {
  case Prooftreea(uu, RuleMacro(n, Prooftreea(s, r, l)), list) =>
    Prooftreea(s, r,
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(map[Prooftree,
                    Prooftree]((aa: Prooftree) => expandProoftree(aa), list),
                a),
                                 map[Prooftree,
                                      Prooftree]((a: Prooftree) =>
           expandProoftree(a),
          l)))
  case Prooftreea(s, RuleCuta(v), list) =>
    Prooftreea(s, RuleCuta(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleLa(v), list) =>
    Prooftreea(s, RuleLa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleStructa(v), list) =>
    Prooftreea(s, RuleStructa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleZera(v), list) =>
    Prooftreea(s, RuleZera(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, Fail(), list) =>
    Prooftreea(s, Fail(),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
}

def rulifyProoftree(x0: Prooftree): Prooftree = x0 match {
  case Prooftreea(s, RuleMacro(str, pt), list) =>
    Prooftreea(rulifySequent(s), RuleMacro(str, rulifyProoftree(pt)),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleCuta(v), list) =>
    Prooftreea(rulifySequent(s), RuleCuta(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleLa(v), list) =>
    Prooftreea(rulifySequent(s), RuleLa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleStructa(v), list) =>
    Prooftreea(rulifySequent(s), RuleStructa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleZera(v), list) =>
    Prooftreea(rulifySequent(s), RuleZera(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, Fail(), list) =>
    Prooftreea(rulifySequent(s), Fail(),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
}

def polarity_Sequent(s: Structure, x1: Sequent): polarity = (s, x1) match {
  case (s, Sequenta(lhs, rhs)) =>
    polarity_weird_xor(polarity_not(polarity_Structure(s, lhs)),
                        polarity_Structure(s, rhs))
  case (s, Sequent_Structure(v)) => N()
}

def collectCutFormulas(x0: Prooftree): List[Formula] = x0 match {
  case Prooftreea(uu, RuleCuta(uv), List(l, r)) =>
    (consq(concl(l)) match {
       case Structure_Bin(_, _, _) =>
         {
           val (Structure_Formula(f)): Structure = consq(concl(r));
           (ant(concl(l)) match {
              case Structure_Bin(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Formula(fa) =>
                (if (equal_Formulaa(f, fa))
                  List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                  else collectCutFormulas(l) ++ collectCutFormulas(r))
              case Structure_Freevar(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Zer(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
            })
         }
       case Structure_Formula(f) =>
         (ant(concl(r)) match {
            case Structure_Bin(_, _, _) =>
              collectCutFormulas(l) ++ collectCutFormulas(r)
            case Structure_Formula(fa) =>
              (if (equal_Formulaa(f, fa))
                List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                else collectCutFormulas(l) ++ collectCutFormulas(r))
            case Structure_Freevar(_) =>
              collectCutFormulas(l) ++ collectCutFormulas(r)
            case Structure_Zer(_) =>
              collectCutFormulas(l) ++ collectCutFormulas(r)
          })
       case Structure_Freevar(_) =>
         {
           val (Structure_Formula(f)): Structure = consq(concl(r));
           (ant(concl(l)) match {
              case Structure_Bin(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Formula(fa) =>
                (if (equal_Formulaa(f, fa))
                  List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                  else collectCutFormulas(l) ++ collectCutFormulas(r))
              case Structure_Freevar(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Zer(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
            })
         }
       case Structure_Zer(_) =>
         {
           val (Structure_Formula(f)): Structure = consq(concl(r));
           (ant(concl(l)) match {
              case Structure_Bin(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Formula(fa) =>
                (if (equal_Formulaa(f, fa))
                  List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                  else collectCutFormulas(l) ++ collectCutFormulas(r))
              case Structure_Freevar(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Zer(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
            })
         }
     })
  case Prooftreea(uw, RuleMacro(ux, pt), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(collectCutFormulas(pt))
  case Prooftreea(uy, RuleLa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleStructa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleZera(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, Fail(), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleCuta(v), Nil) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            Nil)).apply(Nil)
  case Prooftreea(uy, RuleCuta(va), List(v)) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            List(v))).apply(Nil)
  case Prooftreea(uy, RuleCuta(va), v :: vb :: vd :: ve) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            v :: vb :: vd :: ve)).apply(Nil)
}

def collectCutFormulasToLocale(pt: Prooftree): List[Locale] =
  map[Formula, Locale]((a: Formula) => CutFormula(a), collectCutFormulas(pt))

def isProofTreeWithCut(loc: List[Locale], pt: Prooftree): Boolean =
  isProofTree(loc ++ collectCutFormulasToLocale(pt), pt)

def collect_SFAtprop_names(x0: Structure): List[List[Char]] = x0 match {
  case Structure_Formula(Formula_Atprop(Atpropa(x))) => List(x)
  case Structure_Bin(l, oper, r) =>
    collect_SFAtprop_names(l) ++ collect_SFAtprop_names(r)
  case Structure_Formula(Formula_Atprop(Atprop_Freevar(vb))) => Nil
  case Structure_Formula(Formula_Bin(va, vb, vc)) => Nil
  case Structure_Formula(Formula_Freevar(va)) => Nil
  case Structure_Formula(Formula_Un(va, vb)) => Nil
  case Structure_Freevar(v) => Nil
  case Structure_Zer(v) => Nil
}

def sequent_fresh_name(x0: Sequent): Structure = x0 match {
  case Sequenta(l, r) =>
    Structure_Formula(Formula_Atprop(Atpropa(fresh_name(collect_SFAtprop_names(l) ++
                  collect_SFAtprop_names(r)))))
  case Sequent_Structure(v) =>
    Structure_Formula(Formula_Atprop(Atpropa(List('X'))))
}

def equal_polarity(x0: polarity, x1: polarity): Boolean = (x0, x1) match {
  case (Minus(), N()) => false
  case (N(), Minus()) => false
  case (Plus(), N()) => false
  case (N(), Plus()) => false
  case (Plus(), Minus()) => false
  case (Minus(), Plus()) => false
  case (N(), N()) => true
  case (Minus(), Minus()) => true
  case (Plus(), Plus()) => true
}

def position_in_Sequent(s: Structure, x1: Sequent): polarity = (s, x1) match {
  case (s, Sequenta(l, r)) =>
    (if (equal_Structurea(s, l)) Minus()
      else (if (! (equal_polarity(polarity_Structure(s, l), N()))) Minus()
             else (if (equal_Structurea(s, r)) Plus()
                    else (if (! (equal_polarity(polarity_Structure(s, r), N())))
                           Plus() else N()))))
  case (s, Sequent_Structure(v)) => N()
}

def partial_goal_complement(s: Structure, x1: Structure): Structure = (s, x1)
  match {
  case (s, Structure_Bin(l, oper, r)) =>
    (polarity_Structure(s, l) match {
       case Plus() => r
       case Minus() => r
       case N() => (if (equal_Structurea(s, l)) r else l)
     })
  case (s, Structure_Formula(v)) => Structure_Formula(v)
  case (s, Structure_Freevar(v)) => Structure_Freevar(v)
  case (s, Structure_Zer(v)) => Structure_Zer(v)
}

def replace_SFAtprop_into_Structure(sfa: Structure, repl: Structure,
                                     x2: Structure):
      Structure
  =
  (sfa, repl, x2) match {
  case (sfa, repl, Structure_Bin(l, oper, r)) =>
    Structure_Bin(replace_SFAtprop_into_Structure(sfa, repl, l), oper,
                   replace_SFAtprop_into_Structure(sfa, repl, r))
  case (sfa, repl, Structure_Formula(v)) =>
    (if (equal_Structurea(sfa, Structure_Formula(v))) repl
      else Structure_Formula(v))
  case (sfa, repl, Structure_Freevar(v)) =>
    (if (equal_Structurea(sfa, Structure_Freevar(v))) repl
      else Structure_Freevar(v))
  case (sfa, repl, Structure_Zer(v)) =>
    (if (equal_Structurea(sfa, Structure_Zer(v))) repl else Structure_Zer(v))
}

def replace_SFAtprop_into_Sequent(sfa: Structure, repl: Structure, x2: Sequent):
      Sequent
  =
  (sfa, repl, x2) match {
  case (sfa, repl, Sequenta(l, r)) =>
    Sequenta(replace_SFAtprop_into_Structure(sfa, repl, l),
              replace_SFAtprop_into_Structure(sfa, repl, r))
  case (sfa, relp, Sequent_Structure(v)) => Sequent_Structure(v)
}

def replace_SFAtprop_into_PT(sfa: Structure, repl: Structure, x2: Prooftree):
      Prooftree
  =
  (sfa, repl, x2) match {
  case (sfa, repl, Prooftreea(s, r, list)) =>
    Prooftreea(replace_SFAtprop_into_Sequent(sfa, repl, s), r,
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replace_SFAtprop_into_PT(sfa, repl, a),
                                 list))
}

} /* object SequentCalc */
