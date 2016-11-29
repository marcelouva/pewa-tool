/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= null
 * loopUnroll= 3
 * removeQuantifiers= false
 * strictUnrolling= false
 */ 

//-------------- prelude--------------//
module moduleId
open Integer32
open util/sequniv as sequniv
fun fun_reach[h: univ, 
              type: set univ, 
              field: univ -> univ
]: set univ { 
  h.*(field & type->(type+null)) & type 
}
abstract sig char {}
abstract sig Exception{}
one sig E1 extends Exception{}
fun shl[l,r: Int]: Int { l << r } 
fun sshr[l,r: Int]: Int { l >> r } 
fun ushr[l,r: Int]: Int { l >>> r } 

fun fun_univ_equals[
  l:univ, 
  r: univ 
]: boolean { 
  (equ[l,r]) => true else false 
} 

fun fun_set_add[
  l: set univ,
  e: univ
]: set univ { 
  l+e 
} 

fun fun_set_remove[
  l: set univ,
  e: univ
]: set univ {
  l-e
}
fun fun_set_contains[
  l: set univ,
  e: univ
]: boolean {
  (e in l) => true else false 
} 
pred isSubset[
  l: set univ,
  r: set univ
] {
  (l in r) 
} 
pred isNotSubset[
  l: set univ,
  r: set univ
] {
  (l !in r) 
} 
fun fun_set_size[s: set univ]: Int { #s } 

fun fun_not_empty_set[s: set univ]: boolean { (#s = 0) => false else true } 

pred pred_empty_set[l: set univ] { (no l) } 

pred pred_set_some[l: set univ] { some l } 

pred pred_set_one[l: set univ] { one l } 

pred pred_set_lone[l: set univ] { lone l } 


fun fun_set_intersection[
  l: set univ,
  r: set univ
]: set univ {
  l & r 
} 
fun fun_set_difference[
  l: set univ,
  r: set univ
]: set univ {
  l - r 
} 
fun fun_set_sum[
  s: set Int
]: Int {
  sum s 
} 
pred pred_empty_list[l: seq univ] { (no l) } 

fun fun_list_add[
  l: seq univ,
  e: univ
]: seq univ {
  sequniv/add[l,e] 
} 

fun fun_list_get[
  l: seq univ, 
  index: Int
]: univ { 
  index.l 
} 

fun fun_list_contains[
  l: seq univ, 
  e: univ
]: boolean { 
  (e in Int.l) => true else false 
} 

fun fun_list_remove[
  l: seq univ, 
  index: Int
]: seq univ { 
  sequniv/delete[l,index] 
} 

fun fun_list_size[s: seq univ]: Int { #s } 

fun fun_list_equals[
  s1:seq univ, 
  s2: seq univ
]: boolean { 
  (s1=s2) => true else false 
} 

fun fun_list_empty[s: seq univ]: boolean { (#s = 0) => true else false } 

pred pred_empty_map[map: univ -> univ] { (no map) } 

fun fun_map_put[
  map: univ->univ, 
  k: univ, 
  v: univ
]: univ-> univ { 
  map ++ (k->v) 
}

fun fun_map_contains_key[
  map: univ -> univ, 
  k: univ
]: boolean { 
  (some k.map) => true else false 
}

fun fun_map_remove[
  map: univ -> univ, 
  k: univ
]: univ->univ {
  map - (k->univ) 
} 

fun fun_map_get[
  map: univ -> univ, 
  k: univ
]: univ { 
  (some k.map) => k.map else null 
} 

fun fun_map_is_empty[
  map: univ -> univ, 
]: boolean { 
  (some map) => false else true 
}

fun fun_map_clear[
  mapEntries1: univ -> univ -> univ, 
  map: univ
]: univ -> univ -> univ { 
  mapEntries1 - (map -> univ -> univ)
}

fun fun_map_size[
  map: univ -> univ, 
]: univ {
  #map 
} 

pred isEmptyOrNull[u: univ] { u in null } 
fun fun_closure[
  rel: univ -> univ 
]: univ -> univ {
  ^rel 
} 

fun fun_reflexive_closure[
  rel: univ -> univ 
]: univ -> univ {
  *rel 
} 

fun fun_transpose[
  rel: univ -> univ 
]: univ -> univ {
  ~rel 
} 


fun rel_override[
  r:univ->univ,
  k:univ, 
  v:univ
]: univ->univ { 
  r - (k->univ) + (k->v) 
} 


pred pred_in[n: univ, t: set univ] { n in t } 

pred instanceOf[n: univ, t: set univ] { n in t } 

pred isCasteableTo[n: univ, t: set univ] { (n in t) or (n = null) }
abstract sig actionExec{}
pred pos_gen_Int[y:Int]{
 some i: Int | y = i
}
pred pos_gen_I32[y:JavaPrimitiveIntegerValue]{
  some i: JavaPrimitiveIntegerValue | pred_java_primitive_integer_value_eq[y,i]
}
pred pos_add_null[s:JavaPrimitiveIntegerValue,b:boolean]{
   equ[s,null] implies equ[b,false]
   not equ[s,null] implies equ[b,true]
}


pred pos_verify_null[s:JavaPrimitiveIntegerValue+null,b:boolean]{
   equ[s,null] implies equ[b,false]
   not equ[s,null] implies equ[b,true]
}
pred pos_vaciar[s:set univ]{
    no s
}
pred sequence[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue] {
    all x: s.JavaPrimitiveIntegerValue | int32_prevs[x] in s.JavaPrimitiveIntegerValue 
}




pred precondition_Lista_addf[]{}

pred postcondition_Lista_addf[
  intJ_1: JavaPrimitiveIntegerValue,
  thisType_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  thisType_1':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{
  sequence[thisType_1] and sequence[thisType_1'] and
  thisType_1'[i320]=intJ_1  and
  (all a,b:JavaPrimitiveIntegerValue |  
	(a->b) in thisType_1 implies  (fun_java_primitive_integer_value_add[a,i321]->b) in thisType_1') and
        JavaPrimitiveIntegerValue.thisType_1'= JavaPrimitiveIntegerValue.thisType_1 + intJ_1
}
/*scope:1*/



pred precondition_Lista_push[]{}

pred postcondition_Lista_push[
  intJ_1: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{
  sequence[values] and sequence[values'] and
  values'[i320]=intJ_1  and
  (all a,b:JavaPrimitiveIntegerValue |  
	(a->b) in values implies  (fun_java_primitive_integer_value_add[a,i321]->b) in values')
 and
        JavaPrimitiveIntegerValue.values'= JavaPrimitiveIntegerValue.values + intJ_1
}
/*scope:1*/


one
sig Lista_add_first extends actionExec{}
one sig Lista_push extends actionExec{}
pred pred_not[p_0:JavaPrimitiveIntegerValue,p_1:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,p_2:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue]{ not(postcondition_Lista_addf[p_0,p_1,p_2])}
check  programa_wap




fun int32_prevs[e: i320+i321+i322] :set (i320+i321+i322) { e.(   i321->(i320)   +   i322->(i320+i321) )}pred myseq_card[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue, res: JavaPrimitiveIntegerValue] {	let dom = s.JavaPrimitiveIntegerValue |		(no dom and res = i320) or 		(some dom and res = fun_java_primitive_integer_value_add[int32_max[dom],i321])}/*FIN_PRE*/



pred Lista_add_first[
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_addf[]
  and 
  postcondition_Lista_addf[intJ_1_0,
                          thisType_1_0,
                          thisType_1_1]
}


pred gen_intA[
  x_1: Int
]{
  TruePred[]
  and 
  pos_gen_Int[x_1]
}


pred gen_intJ[
  x_1: JavaPrimitiveIntegerValue
]{
  TruePred[]
  and 
  pos_gen_I32[x_1]
}


pred Lista_push[
  intJ_1_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue
]{
  precondition_Lista_push[]
  and 
  postcondition_Lista_push[intJ_1_1,
                          thisType_1_0,
                          thisType_1_1]
}


pred init_set[
  s_1: set univ
]{
  TruePred[]
  and 
  pos_vaciar[s_1]
}


pred verify_null[
  s_0: JavaPrimitiveIntegerValue,
  b_1: boolean
]{
  TruePred[]
  and 
  pos_add_null[s_0,
              b_1]
}


assert programa_wap{
all ac_0 :  actionExec,
    ac_1 :  actionExec,
    ac_2 :  actionExec,
    ac_3 :  actionExec,
    intJ_1_0 :  JavaPrimitiveIntegerValue,
    intJ_1_1 :  JavaPrimitiveIntegerValue,
    intJ_1_2 :  JavaPrimitiveIntegerValue,
    intJ_1_3 :  JavaPrimitiveIntegerValue,
    intJ_1_4 :  JavaPrimitiveIntegerValue,
    intJ_1_5 :  JavaPrimitiveIntegerValue,
    intJ_1_6 :  JavaPrimitiveIntegerValue,
    thisType_1_0 :  JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
    thisType_1_1 :  JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
    thisType_1_2 :  JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
    thisType_1_3 :  JavaPrimitiveIntegerValue -> lone JavaPrimitiveIntegerValue,
    valid_bool_1 :  boolean,
    valid_intA_1 :  boolean,
    valid_intJ_1 :  boolean | {
  (
    precondition_Lista_addf[]
    and 
    (
      valid_intA_1=false)
    and 
    (
      valid_bool_1=false)
    and 
    (
      valid_intJ_1=false)
    and 
    (
      (
        gen_intJ[intJ_1_1]
        and 
        Lista_push[intJ_1_2,
                  thisType_1_0,
                  thisType_1_1]
        and 
        (
          ac_1=Lista_push)
      )
      or 
      (
        TruePred[]
        and 
        (
          ac_0=ac_1)
        and 
        (
          thisType_1_0=thisType_1_1)
        and 
        (
          intJ_1_0=intJ_1_2)
      )
    )
    and 
    (
      (
        gen_intJ[intJ_1_3]
        and 
        Lista_push[intJ_1_4,
                  thisType_1_1,
                  thisType_1_2]
        and 
        (
          ac_2=Lista_push)
      )
      or 
      (
        TruePred[]
        and 
        (
          ac_1=ac_2)
        and 
        (
          thisType_1_1=thisType_1_2)
        and 
        (
          intJ_1_2=intJ_1_4)
      )
    )
    and 
    (
      (
        gen_intJ[intJ_1_5]
        and 
        Lista_push[intJ_1_6,
                  thisType_1_2,
                  thisType_1_3]
        and 
        (
          ac_3=Lista_push)
      )
      or 
      (
        TruePred[]
        and 
        (
          ac_2=ac_3)
        and 
        (
          thisType_1_2=thisType_1_3)
        and 
        (
          intJ_1_4=intJ_1_6)
      )
    )
  )
  implies 
          pred_not[intJ_1_0,
                  thisType_1_0,
                  thisType_1_3]
  }
}
