open util/integer
open util/boolean 


sig Request {
	issuer : one Third_party,
	result : lone Result,
	accepted : one Bool,
	}

sig Result {
	request: one Request} 


sig User {}

sig Individual_Request extends Request {
	Individual_Req_concern: one Individual,
}


sig Group_Request extends Request {
	Group_Req_concern: some Individual
}


sig Third_party extends User {
	Ind_request_issued: set Individual_Request ,
	Anonym_request_issued: set Group_Request
	}

sig Individual extends User {
	Request_received: set Individual_Request
}


fact unique_individual_per_ind_request {
-- two disjoint individuals cannot be concerned by the same individual request
all ind, ind' : Individual | no ind_r:Individual_Request | ind != ind' and ind_r in (ind.Request_received & ind'.Request_received)}



fact unique_third_party_per_ind_request {
-- two third parties cannot produce the same individual request
all third, third' : Third_party | no req : Individual_Request | third != third' and req in (third.Ind_request_issued & third.Ind_request_issued)}


fact reciprocity_for_request {
--if a third party is linked to a request then the Request must linked to the third party
all req:Request, third:Third_party | (req in (third.Ind_request_issued + third.Anonym_request_issued)) iff (third in req.issuer) }



fact reciprocity_for_ind {
--if an individual is linked to an  individual_request then the ind_request must linked to ind
all req:Request, ind:Individual | (req in ind.Request_received) iff (ind in req.	Individual_Req_concern)}



fact unique_result {
-- two disjoint request cannot produce the same result
all req, req' : Request | no res:Result | req!=req' and res in (req.result & req'.result)}



fact unique_request {
-- two disjoint results cannot come from the same request 
all res, res' : Result | no req:Request | res!=res' and req in (res.request & res'.request)}



fact acceptance_implies_result {
--request accepted implies result AND request refused implies no result 
all req : Request | (req.accepted = True iff req.result != none)  and (req.accepted =False iff req.result = none)}



fact result_reciprocity {
all req : Request, res : Result | (req in res.request) iff (res in req.result)}



fact individuals_concernded_by_group_request {
-- at least 1000 for a group request to be accepted
--modelised by 2
(all req: Group_Request | req.accepted=True iff #req.Group_Req_concern >=2) }


pred show1{}

pred show2 {#Group_Request>=1
				   	#Individual_Request>=1
					#Individual>=3
					#result >=2
					(one gr:Group_Request | #gr.Group_Req_concern>= 3)
				 } 


 run show1
