sig Request {
	issuer : one Third_party
	}

sig Result {} 
sig User {}

sig Individual_Request extends Request {
	Individual_Req_concern: one Individual,
}


sig Group_Request extends Request {
	Group_Req_concern: some Individual}


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
all req:Request, third:Third_party | ((req in (third.Ind_request_issued + third.Anonym_request_issued)) implies (third in req.issuer)) and ( (third in req.issuer) implies(req in (third.Ind_request_issued + third.Anonym_request_issued)))}


fact reciprocity_for_ind {
--if an individual is linked to an  individual_request then the ind_request must linked to ind
all req:Request, ind:Individual | ((req in ind.Request_received) implies (ind in req.	Individual_Req_concern)) and ((ind in req.Individual_Req_concern) implies(req in ind.Request_received))}




pred show [] {}
 run show 

