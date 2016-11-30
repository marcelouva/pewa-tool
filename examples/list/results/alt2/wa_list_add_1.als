module SListInt32MySeq

open Integer32



one sig SListInt32MySeq  {}

abstract sig SListInt32Node {}


one sig QF {intJ_1_0:JavaPrimitiveIntegerValue,intJ_1_1:JavaPrimitiveIntegerValue,intJ_2_0:JavaPrimitiveIntegerValue,intJ_2_1:JavaPrimitiveIntegerValue,return_intJ_1_1:JavaPrimitiveIntegerValue,return_intJ_2_1:JavaPrimitiveIntegerValue,return_bool_1:boolean,
  thisType_1_0: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  thiz_0:      one SListInt32MySeq,
  head_0:      SListInt32MySeq ->one(SListInt32Node+null),
  nodeValue_0: SListInt32Node ->one(JavaPrimitiveIntegerValue+null),
  index_0: SListInt32Node -> lone JavaPrimitiveIntegerValue,
  fnext_0:     SListInt32Node ->lone(SListInt32Node+null),
  bnext_0:     SListInt32Node ->lone(SListInt32Node+null),
  size_0:      SListInt32MySeq ->one JavaPrimitiveIntegerValue,
}


fact repOk {
  let next = QF.fnext_0+QF.bnext_0,
      thiz = QF.thiz_0,
      head = QF.head_0,
      value = QF.nodeValue_0,
      index = QF.index_0 |
  {
    // no cycles 
    all n: thiz.head.*next-null | { n !in n.next.*next and n.value != null }
    // compute indexes for nodes
    (thiz.head!=null => thiz.head.index = i320
                             and
                             (all n1,n2: thiz.head.*next-null | n1.next = n2 implies fun_java_primitive_integer_value_add[n1.index,i321] = n2.index)
    )
    
  }
}


pred sequence[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue] {
    all x: s.JavaPrimitiveIntegerValue | int32_prevs[x] in s.JavaPrimitiveIntegerValue 
}


fact {
    sequence[QF.thisType_1_0]
    sequence[QF.thisType_1_1]
}


fact abstraction {
  let thiz = QF.thiz_0,
      size = QF.size_0, 
      value = QF.nodeValue_0,
      index = QF.index_0,
      myseq = QF.thisType_1_1 |
  {
    (myseq_card[myseq, thiz.size])
    and
    (all i: myseq.JavaPrimitiveIntegerValue | i.myseq = index.i.value)
  }
}


fact {
  all a, b: JavaPrimitiveIntegerValue | 
    (a = b <=> pred_java_primitive_integer_value_eq[a,b]) 
--    ( pred_java_primitive_integer_value_eq[a,b]) 

}


//fact orderingAxiom1 
fact { 
let entry=(QF.thiz_0).(QF.head_0),ff1=QF.fnext_0,bf1=QF.bnext_0 | { 
-- forwardPlusBackwardAreFunctions
no ((ff1.univ) & (bf1.univ)) 
N0+N1+N2+N3+N4+N5+N6+N7 = ff1.univ + bf1.univ 
--forwardIsIndeedForward 
entry in N0+null 
all n : entry.*ff1 - null | node_min[ff1.n] in node_prevs[n] 
all disj n1, n2 : entry.*ff1 - null | 
{ 
      ( some (ff1.n1 ) && some (ff1.n2 ) && node_min[ff1.n1 ] in 
      node_prevs[node_min[ff1.n2 ]] ) 
        implies n1 in node_prevs[n2] 
  } 
  --backwardsIsIndeedBackwards 
   (bf1 in node_relprevs)
  --prefixReachableForward 
    all x : entry.*(ff1) -null | node_prevs[x] in entry.*(ff1) 
} 
} 



fact fixReachable {all n : SListInt32Node | n !in (QF.thiz_0).(QF.head_0).*(QF.fnext_0) implies
		(
			n.(QF.nodeValue_0) = i320 and
            no n.(QF.index_0) and
			n.(QF.fnext_0) = null and
			no n.(QF.bnext_0)
		)
}


fun FReach[] :set (N0+N1+N2+N3+N4+N5+N6+N7) {
    (QF.thiz_0).(QF.head_0).*(QF.fnext_0)-null
}

one sig N0,N1,N2,N3,N4,N5,N6,N7 extends SListInt32Node {}




fact { QF.fnext_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->null+N4->N5+N4->N6+N4->N7+N4->null+N5->N6+N5->N7+N5->null+N6->N7+N6->null+N7->null }
fact { QF.bnext_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7 }


fact {
	(QF.index_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->null
}


fact {
	(QF.size_0) in SListInt32MySeq->i320+SListInt32MySeq->i321+SListInt32MySeq->i322+SListInt32MySeq->i323+SListInt32MySeq->i324+SListInt32MySeq->i325+SListInt32MySeq->i326+SListInt32MySeq->i327+SListInt32MySeq->i328
}




// myseq definitions
fun int32_max[es: set (i320+i321+i322+i323+i324+i325+i326+i327)] : lone (i320+i321+i322+i323+i324+i325+i326+i327) {
 es - es.(
   i321->(i320)
   +
   i322->(i320+i321)
   +
   i323->(i320+i321+i322)
   +
   i324->(i320+i321+i322+i323)
   +
   i325->(i320+i321+i322+i323+i324)
   +
   i326->(i320+i321+i322+i323+i324+i325)
   +
   i327->(i320+i321+i322+i323+i324+i325+i326)
 )
}


fun int32_prevs[e: i320+i321+i322+i323+i324+i325+i326+i327] :set (i320+i321+i322+i323+i324+i325+i326+i327) {
 e.(
   i321->(i320)
   +
   i322->(i320+i321)
   +
   i323->(i320+i321+i322)
   +
   i324->(i320+i321+i322+i323)
   +
   i325->(i320+i321+i322+i323+i324)
   +
   i326->(i320+i321+i322+i323+i324+i325)
   +
   i327->(i320+i321+i322+i323+i324+i325+i326)
 )
}


pred myseq_card[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue, res: JavaPrimitiveIntegerValue] {
	let dom = s.JavaPrimitiveIntegerValue |
		(no dom and res = i320) or 
		(some dom and res = fun_java_primitive_integer_value_add[int32_max[dom],i321])
}


// end of myseq definitions


fun node_max[es: set (N0+N1+N2+N3+N4+N5+N6+N7)] : lone (N0+N1+N2+N3+N4+N5+N6+N7) {
 es - es.(
   N1->(N0)
   +
   N2->(N0+N1)
   +
   N3->(N0+N1+N2)
   +
   N4->(N0+N1+N2+N3)
   +
   N5->(N0+N1+N2+N3+N4)
   +
   N6->(N0+N1+N2+N3+N4+N5)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6)
 )
}


fact mysize {
	let m = node_max[FReach[]-null], size = (QF.thiz_0).(QF.size_0) | 
	  (no m and size = i320) or 
	  (m = N0 and size = i321) or
	  (m = N1 and size = i322) or
	  (m = N2 and size = i323) or
	  (m = N3 and size = i324) or
	  (m = N4 and size = i325) or
	  (m = N5 and size = i326) or
	  (m = N6 and size = i327) or
	  (m = N7 and size = i328)

}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 SListInt32MySeq, exactly 8 SListInt32Node, 1 int, exactly 15  JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7) -> lone (N0+N1+N2+N3+N4+N5+N6+N7) {
 N0->N1
 +
 N1->N2
 +
 N2->N3
 +
 N3->N4
 +
 N4->N5
 +
 N5->N6
 +
 N6->N7
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7] :set (N0+N1+N2+N3+N4+N5+N6+N7) {
 e.(
   N1->(N0)
   +
   N2->(N0+N1)
   +
   N3->(N0+N1+N2)
   +
   N4->(N0+N1+N2+N3)
   +
   N5->(N0+N1+N2+N3+N4)
   +
   N6->(N0+N1+N2+N3+N4+N5)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6)
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7] :set (N0+N1+N2+N3+N4+N5+N6+N7) {
 e.(
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
   +
   N3->(N0+N1+N2+N3)
   +
   N4->(N0+N1+N2+N3+N4)
   +
   N5->(N0+N1+N2+N3+N4+N5)
   +
   N6->(N0+N1+N2+N3+N4+N5+N6)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6+N7)
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5+N6+N7) -> set (N0+N1+N2+N3+N4+N5+N6+N7) {
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
   +
   N3->(N0+N1+N2+N3)
   +
   N4->(N0+N1+N2+N3+N4)
   +
   N5->(N0+N1+N2+N3+N4+N5)
   +
   N6->(N0+N1+N2+N3+N4+N5+N6)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6+N7)
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5+N6+N7)] : lone (N0+N1+N2+N3+N4+N5+N6+N7) {
 es - es.(
   N0->(N1+N2+N3+N4+N5+N6+N7)
   +
   N1->(N2+N3+N4+N5+N6+N7)
   +
   N2->(N3+N4+N5+N6+N7)
   +
   N3->(N4+N5+N6+N7)
   +
   N4->(N5+N6+N7)
   +
   N5->(N6+N7)
   +
   N6->(N7)
 )
}




fact{ 

//Bound for field QF.head_0: 
QF.head_0 in SListInt32MySeq->null + SListInt32MySeq->N0

//Bound for field QF.index_0: 
QF.index_0 in N0->i320 + N1->i321 + N2->i322 + N3->i323 + N4->i324 + N5->i325 + N6->i326 + N7->i327

//Bound for field QF.fnext_0: 
QF.fnext_0 in N0->null + N0->N1 + N1->null + N1->N2 + N2->null + N2->N3 + N3->null + N3->N4 + N4->null + N4->N5 + N5->null + N5->N6 + N6->null + N6->N7 + N7->null

//Bound for field QF.bnext_0: 
QF.bnext_0 in none->none

//Bound for field QF.size_0: 
QF.size_0 in SListInt32MySeq->i320 + SListInt32MySeq->i321 + SListInt32MySeq->i322 + SListInt32MySeq->i323 + SListInt32MySeq->i324 + SListInt32MySeq->i325 + SListInt32MySeq->i326 + SListInt32MySeq->i327 + SListInt32MySeq->i328

}
pred precondition_Lista_add[]{}

pred postcondition_Lista_add[
  intJ_1: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue
]
{
  sequence[values] and
  (some size:JavaPrimitiveIntegerValue | myseq_card[values,size] and  values'=values+(size->intJ_1))
}



 fact{ precondition_Lista_add[]
postcondition_Lista_add[QF.intJ_1_0,QF.thisType_1_0,QF.thisType_1_1]
}
fact{QF.thisType_1_0 in ( i320->i321)+( i321->i3244400)+( i322->i3210)+( i323->i32500)+( i324->i32m700)+( i325->i326)+( i326->i32m6) and ( i320->i321)+( i321->i3244400)+( i322->i3210)+( i323->i32500)+( i324->i32m700)+( i325->i326)+( i326->i32m6) in QF.thisType_1_0}  one sig i320  extends JavaPrimitiveIntegerValue{}  one sig i321  extends JavaPrimitiveIntegerValue{}  one sig i322  extends JavaPrimitiveIntegerValue{}  one sig i323  extends JavaPrimitiveIntegerValue{}  one sig i324  extends JavaPrimitiveIntegerValue{}  one sig i325  extends JavaPrimitiveIntegerValue{}  one sig i326  extends JavaPrimitiveIntegerValue{}  one sig i327  extends JavaPrimitiveIntegerValue{}  one sig i32500  extends JavaPrimitiveIntegerValue{}  one sig i328  extends JavaPrimitiveIntegerValue{}  one sig i32m700  extends JavaPrimitiveIntegerValue{}  one sig i3210  extends JavaPrimitiveIntegerValue{}  one sig i3244400  extends JavaPrimitiveIntegerValue{}  one sig i32m6  extends JavaPrimitiveIntegerValue{}  one sig i32m1  extends JavaPrimitiveIntegerValue{}  fact{ b00 in i320->false  + i321->true  + i322->false  + i323->true  + i324->false  + i325->true  + i326->false  + i327->true  + i32500->false  + i328->false  + i32m700->false  + i3210->false  + i3244400->false  + i32m6->false  + i32m1->true  and i320->false  + i321->true  + i322->false  + i323->true  + i324->false  + i325->true  + i326->false  + i327->true  + i32500->false  + i328->false  + i32m700->false  + i3210->false  + i3244400->false  + i32m6->false  + i32m1->true  in  b00 and  b01 in i320->false  + i321->false  + i322->true  + i323->true  + i324->false  + i325->false  + i326->true  + i327->true  + i32500->false  + i328->false  + i32m700->false  + i3210->true  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->true  + i323->true  + i324->false  + i325->false  + i326->true  + i327->true  + i32500->false  + i328->false  + i32m700->false  + i3210->true  + i3244400->false  + i32m6->true  + i32m1->true  in  b01 and  b02 in i320->false  + i321->false  + i322->false  + i323->false  + i324->true  + i325->true  + i326->true  + i327->true  + i32500->true  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->false  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->true  + i325->true  + i326->true  + i327->true  + i32500->true  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->false  + i32m1->true  in  b02 and  b03 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->true  + i32m700->false  + i3210->true  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->true  + i32m700->false  + i3210->true  + i3244400->false  + i32m6->true  + i32m1->true  in  b03 and  b04 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->true  + i328->false  + i32m700->false  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->true  + i328->false  + i32m700->false  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  in  b04 and  b05 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->true  + i328->false  + i32m700->false  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->true  + i328->false  + i32m700->false  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  in  b05 and  b06 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->true  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->true  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  in  b06 and  b07 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->true  + i328->false  + i32m700->false  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->true  + i328->false  + i32m700->false  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in  b07 and  b08 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->true  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->true  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  in  b08 and  b09 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->false  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->false  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in  b09 and b10 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  in b10 and b11 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  in b11 and b12 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b12 and b13 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  in b13 and b14 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b14 and b15 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->true  + i32m6->true  + i32m1->true  in b15 and b16 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b16 and b17 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b17 and b18 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b18 and b19 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b19 and b20 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b20 and b21 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b21 and b22 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b22 and b23 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b23 and b24 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b24 and b25 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b25 and b26 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b26 and b27 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b27 and b28 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b28 and b29 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b29 and b30 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b30 and b31 in i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  and i320->false  + i321->false  + i322->false  + i323->false  + i324->false  + i325->false  + i326->false  + i327->false  + i32500->false  + i328->false  + i32m700->true  + i3210->false  + i3244400->false  + i32m6->true  + i32m1->true  in b31} fact { QF.intJ_1_0=i325} 