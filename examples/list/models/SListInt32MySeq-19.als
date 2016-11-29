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
N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18 = ff1.univ + bf1.univ 
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


fun FReach[] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18) {
    (QF.thiz_0).(QF.head_0).*(QF.fnext_0)-null
}

one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18 extends SListInt32Node {}




fact { QF.fnext_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->N13+N0->N14+N0->N15+N0->N16+N0->N17+N0->N18+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->N13+N1->N14+N1->N15+N1->N16+N1->N17+N1->N18+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->N13+N2->N14+N2->N15+N2->N16+N2->N17+N2->N18+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->N13+N3->N14+N3->N15+N3->N16+N3->N17+N3->N18+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->N13+N4->N14+N4->N15+N4->N16+N4->N17+N4->N18+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->N13+N5->N14+N5->N15+N5->N16+N5->N17+N5->N18+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->N13+N6->N14+N6->N15+N6->N16+N6->N17+N6->N18+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->N13+N7->N14+N7->N15+N7->N16+N7->N17+N7->N18+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->N13+N8->N14+N8->N15+N8->N16+N8->N17+N8->N18+N8->null+N9->N10+N9->N11+N9->N12+N9->N13+N9->N14+N9->N15+N9->N16+N9->N17+N9->N18+N9->null+N10->N11+N10->N12+N10->N13+N10->N14+N10->N15+N10->N16+N10->N17+N10->N18+N10->null+N11->N12+N11->N13+N11->N14+N11->N15+N11->N16+N11->N17+N11->N18+N11->null+N12->N13+N12->N14+N12->N15+N12->N16+N12->N17+N12->N18+N12->null+N13->N14+N13->N15+N13->N16+N13->N17+N13->N18+N13->null+N14->N15+N14->N16+N14->N17+N14->N18+N14->null+N15->N16+N15->N17+N15->N18+N15->null+N16->N17+N16->N18+N16->null+N17->N18+N17->null+N18->null }
fact { QF.bnext_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12+N13->N0+N13->N1+N13->N2+N13->N3+N13->N4+N13->N5+N13->N6+N13->N7+N13->N8+N13->N9+N13->N10+N13->N11+N13->N12+N13->N13+N14->N0+N14->N1+N14->N2+N14->N3+N14->N4+N14->N5+N14->N6+N14->N7+N14->N8+N14->N9+N14->N10+N14->N11+N14->N12+N14->N13+N14->N14+N15->N0+N15->N1+N15->N2+N15->N3+N15->N4+N15->N5+N15->N6+N15->N7+N15->N8+N15->N9+N15->N10+N15->N11+N15->N12+N15->N13+N15->N14+N15->N15+N16->N0+N16->N1+N16->N2+N16->N3+N16->N4+N16->N5+N16->N6+N16->N7+N16->N8+N16->N9+N16->N10+N16->N11+N16->N12+N16->N13+N16->N14+N16->N15+N16->N16+N17->N0+N17->N1+N17->N2+N17->N3+N17->N4+N17->N5+N17->N6+N17->N7+N17->N8+N17->N9+N17->N10+N17->N11+N17->N12+N17->N13+N17->N14+N17->N15+N17->N16+N17->N17+N18->N0+N18->N1+N18->N2+N18->N3+N18->N4+N18->N5+N18->N6+N18->N7+N18->N8+N18->N9+N18->N10+N18->N11+N18->N12+N18->N13+N18->N14+N18->N15+N18->N16+N18->N17+N18->N18 }


fact {
	(QF.index_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->i3212+N0->i3213+N0->i3214+N0->i3215+N0->i3216+N0->i3217+N0->i3218+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->i3212+N1->i3213+N1->i3214+N1->i3215+N1->i3216+N1->i3217+N1->i3218+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->i3212+N2->i3213+N2->i3214+N2->i3215+N2->i3216+N2->i3217+N2->i3218+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->i3212+N3->i3213+N3->i3214+N3->i3215+N3->i3216+N3->i3217+N3->i3218+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->i3212+N4->i3213+N4->i3214+N4->i3215+N4->i3216+N4->i3217+N4->i3218+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->i3212+N5->i3213+N5->i3214+N5->i3215+N5->i3216+N5->i3217+N5->i3218+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->i3212+N6->i3213+N6->i3214+N6->i3215+N6->i3216+N6->i3217+N6->i3218+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->i3212+N7->i3213+N7->i3214+N7->i3215+N7->i3216+N7->i3217+N7->i3218+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->i3212+N8->i3213+N8->i3214+N8->i3215+N8->i3216+N8->i3217+N8->i3218+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->i3212+N9->i3213+N9->i3214+N9->i3215+N9->i3216+N9->i3217+N9->i3218+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->i3212+N10->i3213+N10->i3214+N10->i3215+N10->i3216+N10->i3217+N10->i3218+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->i3212+N11->i3213+N11->i3214+N11->i3215+N11->i3216+N11->i3217+N11->i3218+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->i3212+N12->i3213+N12->i3214+N12->i3215+N12->i3216+N12->i3217+N12->i3218+N12->null+N13->i320+N13->i321+N13->i322+N13->i323+N13->i324+N13->i325+N13->i326+N13->i327+N13->i328+N13->i329+N13->i3210+N13->i3211+N13->i3212+N13->i3213+N13->i3214+N13->i3215+N13->i3216+N13->i3217+N13->i3218+N13->null+N14->i320+N14->i321+N14->i322+N14->i323+N14->i324+N14->i325+N14->i326+N14->i327+N14->i328+N14->i329+N14->i3210+N14->i3211+N14->i3212+N14->i3213+N14->i3214+N14->i3215+N14->i3216+N14->i3217+N14->i3218+N14->null+N15->i320+N15->i321+N15->i322+N15->i323+N15->i324+N15->i325+N15->i326+N15->i327+N15->i328+N15->i329+N15->i3210+N15->i3211+N15->i3212+N15->i3213+N15->i3214+N15->i3215+N15->i3216+N15->i3217+N15->i3218+N15->null+N16->i320+N16->i321+N16->i322+N16->i323+N16->i324+N16->i325+N16->i326+N16->i327+N16->i328+N16->i329+N16->i3210+N16->i3211+N16->i3212+N16->i3213+N16->i3214+N16->i3215+N16->i3216+N16->i3217+N16->i3218+N16->null+N17->i320+N17->i321+N17->i322+N17->i323+N17->i324+N17->i325+N17->i326+N17->i327+N17->i328+N17->i329+N17->i3210+N17->i3211+N17->i3212+N17->i3213+N17->i3214+N17->i3215+N17->i3216+N17->i3217+N17->i3218+N17->null+N18->i320+N18->i321+N18->i322+N18->i323+N18->i324+N18->i325+N18->i326+N18->i327+N18->i328+N18->i329+N18->i3210+N18->i3211+N18->i3212+N18->i3213+N18->i3214+N18->i3215+N18->i3216+N18->i3217+N18->i3218+N18->null
}


fact {
	(QF.size_0) in SListInt32MySeq->i320+SListInt32MySeq->i321+SListInt32MySeq->i322+SListInt32MySeq->i323+SListInt32MySeq->i324+SListInt32MySeq->i325+SListInt32MySeq->i326+SListInt32MySeq->i327+SListInt32MySeq->i328+SListInt32MySeq->i329+SListInt32MySeq->i3210+SListInt32MySeq->i3211+SListInt32MySeq->i3212+SListInt32MySeq->i3213+SListInt32MySeq->i3214+SListInt32MySeq->i3215+SListInt32MySeq->i3216+SListInt32MySeq->i3217+SListInt32MySeq->i3218+SListInt32MySeq->i3219
}




// myseq definitions
fun int32_max[es: set (i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217+i3218)] : lone (i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217+i3218) {
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
   +
   i328->(i320+i321+i322+i323+i324+i325+i326+i327)
   +
   i329->(i320+i321+i322+i323+i324+i325+i326+i327+i328)
   +
   i3210->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329)
   +
   i3211->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210)
   +
   i3212->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211)
   +
   i3213->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212)
   +
   i3214->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213)
   +
   i3215->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214)
   +
   i3216->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215)
   +
   i3217->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216)
   +
   i3218->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217)
 )
}


fun int32_prevs[e: i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217+i3218] :set (i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217+i3218) {
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
   +
   i328->(i320+i321+i322+i323+i324+i325+i326+i327)
   +
   i329->(i320+i321+i322+i323+i324+i325+i326+i327+i328)
   +
   i3210->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329)
   +
   i3211->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210)
   +
   i3212->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211)
   +
   i3213->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212)
   +
   i3214->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213)
   +
   i3215->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214)
   +
   i3216->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215)
   +
   i3217->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216)
   +
   i3218->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212+i3213+i3214+i3215+i3216+i3217)
 )
}


pred myseq_card[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue, res: JavaPrimitiveIntegerValue] {
	let dom = s.JavaPrimitiveIntegerValue |
		(no dom and res = i320) or 
		(some dom and res = fun_java_primitive_integer_value_add[int32_max[dom],i321])
}


// end of myseq definitions


fun node_max[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18) {
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
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7)
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N13->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N14->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N15->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)
   +
   N16->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15)
   +
   N17->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16)
   +
   N18->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17)
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
	  (m = N7 and size = i328) or
	  (m = N8 and size = i329) or
	  (m = N9 and size = i3210) or
	  (m = N10 and size = i3211) or
	  (m = N11 and size = i3212) or
	  (m = N12 and size = i3213) or
	  (m = N13 and size = i3214) or
	  (m = N14 and size = i3215) or
	  (m = N15 and size = i3216) or
	  (m = N16 and size = i3217) or
	  (m = N17 and size = i3218) or
	  (m = N18 and size = i3219)

}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 SListInt32MySeq, exactly 19 SListInt32Node, 1 int, exactly 20 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18) {
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
 +
 N7->N8
 +
 N8->N9
 +
 N9->N10
 +
 N10->N11
 +
 N11->N12
 +
 N12->N13
 +
 N13->N14
 +
 N14->N15
 +
 N15->N16
 +
 N16->N17
 +
 N17->N18
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18) {
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
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7)
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N13->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N14->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N15->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)
   +
   N16->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15)
   +
   N17->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16)
   +
   N18->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17)
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18) {
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
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N13->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N14->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)
   +
   N15->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15)
   +
   N16->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16)
   +
   N17->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17)
   +
   N18->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18) -> set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18) {
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
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N13->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13)
   +
   N14->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)
   +
   N15->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15)
   +
   N16->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16)
   +
   N17->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17)
   +
   N18->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18) {
 es - es.(
   N0->(N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N1->(N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N2->(N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N3->(N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N4->(N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N5->(N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N6->(N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N7->(N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N8->(N9+N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N9->(N10+N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N10->(N11+N12+N13+N14+N15+N16+N17+N18)
   +
   N11->(N12+N13+N14+N15+N16+N17+N18)
   +
   N12->(N13+N14+N15+N16+N17+N18)
   +
   N13->(N14+N15+N16+N17+N18)
   +
   N14->(N15+N16+N17+N18)
   +
   N15->(N16+N17+N18)
   +
   N16->(N17+N18)
   +
   N17->(N18)
 )
}




fact{ 

//Bound for field QF.head_0: 
QF.head_0 in SListInt32MySeq->null + SListInt32MySeq->N0

//Bound for field QF.index_0: 
QF.index_0 in N0->i320 + N1->i321 + N2->i322 + N3->i323 + N4->i324 + N5->i325 + N6->i326 + N7->i327 + N8->i328 + N9->i329 + N10->i3210 + N11->i3211 + N12->i3212 + N13->i3213 + N14->i3214 + N15->i3215 + N16->i3216 + N17->i3217 + N18->i3218

//Bound for field QF.fnext_0: 
QF.fnext_0 in N0->null + N0->N1 + N1->null + N1->N2 + N2->null + N2->N3 + N3->null + N3->N4 + N4->null + N4->N5 + N5->null + N5->N6 + N6->null + N6->N7 + N7->null + N7->N8 + N8->null + N8->N9 + N9->null + N9->N10 + N10->null + N10->N11 + N11->null + N11->N12 + N12->null + N12->N13 + N13->null + N13->N14 + N14->null + N14->N15 + N15->null + N15->N16 + N16->null + N16->N17 + N17->null + N17->N18 + N18->null

//Bound for field QF.bnext_0: 
QF.bnext_0 in none->none

//Bound for field QF.size_0: 
QF.size_0 in SListInt32MySeq->i320 + SListInt32MySeq->i321 + SListInt32MySeq->i322 + SListInt32MySeq->i323 + SListInt32MySeq->i324 + SListInt32MySeq->i325 + SListInt32MySeq->i326 + SListInt32MySeq->i327 + SListInt32MySeq->i328 + SListInt32MySeq->i329 + SListInt32MySeq->i3210 + SListInt32MySeq->i3211 + SListInt32MySeq->i3212 + SListInt32MySeq->i3213 + SListInt32MySeq->i3214 + SListInt32MySeq->i3215 + SListInt32MySeq->i3216 + SListInt32MySeq->i3217 + SListInt32MySeq->i3218 + SListInt32MySeq->i3219

}
