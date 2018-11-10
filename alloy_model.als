open util/integer
open util/boolean 

/**************************           SIGNATURES         **************************/

sig Request {
/* A request has tree attributes: 
- the issuer = The third party that made the request. A request must be done by one and only one third party
- the result = The result produced by the request. A request can produce no result if it has been refused, and must produce one if accepted
- accepted = The status of the resquest (True is it has been accepted, False otherwise).

There are two types of requests :
 - anonymised request
 - individual request								 
*/
	issuer : one Third_party,
	accepted : one Bool,
	}

sig Result {
/* the result of a request exists only if the request has been accepted*/
} 

sig Anonymised_Result extends Result {
/* the result of a request exists only if the request has been accepted*/
	data: some Data, /*an anonymised result contains the data of all the individuals concerned by the request*/
} 

sig Individual_Result extends Result {
/* the result of a request exists only if the request has been accepted*/
	data: one Data,/*an individual result contains the data the individual concerned by the request*/
} 

sig User {
/* a user can be an Individual or a third party*/}

sig Individual_Request extends Request {
 /* An individual request is a request concerning one and only one individuals*/
	Individual_Req_concern: one Individual,
	result:lone Individual_Result
}


sig Anonymised_Request extends Request {
/* An anonymised request is a request concerning a group of individuals*/
	Anonymised_Req_concern: some Individual,
	result:lone Anonymised_Result
}

sig Data{}

sig Third_party extends User {
/* A third party is a type of user that is able to make requests.
A third party can make has much requests has he wants. Thoses requests can be anonymised requests or individual requests. 
*/
	Ind_request_issued: set Individual_Request ,
	Anonym_request_issued: set Anonymised_Request
/*An individual also has a name, an identificator, an adress, a phone number etc
but as the goal of this model is to verify the interactions bettwen the individuals, the third parties and the requests,
 we thought that adding these attributes would not be relevant because it would not prove anything and 
it would make reading more difficult */
	}

sig Individual extends User {
/* An individual is a type of user that is NOT able to make requests.
An individual see the requests he receive and has to answering them by accpeting or refusing them*/
	Request_received: set Individual_Request,
	data: one Data,
/*An individual also has a name, a surname, a fiscal code, an age, an adress, a phone number etc
but as the goal of this model is to verify the interactions bettwen the individuals, the third parties and the requests,
 we thought that adding these attributes would not be relevant because it would not prove anything and 
it would make reading more difficult */
}




/******************************         FACTS    ***********************************/

/**ABOUT INDIVIDUAL REQUESTS **********/

fact unique_individual_per_ind_request {
/*two disjoint individuals cannot be receive the same individual request*/
all ind, ind' : Individual | no ind_r:Individual_Request | ind != ind' and ind_r in (ind.Request_received & ind'.Request_received)}


fact reciprocity_for_ind_and_requests {
--if an individual is linked to an  individual_request then the ind_request must linked to ind
all req:Request, ind:Individual | (req in ind.Request_received) iff (ind in req.Individual_Req_concern)}

/**ABOUT THIRD PARTIES**********/

fact reciprocity_for_requests_and_third_parties {
/*if a third party is linked to a request then the Request must linked to the third party*/
all req:Request, third:Third_party | (req in (third.Ind_request_issued + third.Anonym_request_issued)) iff (third in req.issuer) }

fact unique_third_party_per_request {
/*two third parties cannot produce the same request.
Indeed, a request male a unique connection between ONE individual, ONE third party and if accepted ONE result*/
all third, third' : Third_party | no req : Request | third != third' and req in (third.Ind_request_issued & third'.Ind_request_issued)}

/** ABOUT RESULTS ************/

fact unique_result_anon {
/*two disjoint requests cannot produce the same result
Indeed, any anonymised request produces its own result*/ 
all req, req' : Anonymised_Request | no res:Anonymised_Result | req!=req' and res in (req.result & req'.result)}


fact unique_result_ind {
/*two disjoint requests cannot produce the same result
Indeed, any  individual request produces its own result*/ 
all req, req' : Individual_Request | no res:Individual_Result | req!=req' and res in (req.result & req'.result)}


fact acceptance_implies_result_anon {
/* (If an anonymised request is accepted THEN the request must produce a result) AND (if an anonymised request is refused THEN it cannot produce a result)*/
all req : Anonymised_Request | (req.accepted = True iff req.result != none)  and (req.accepted =False iff req.result = none)}


fact acceptance_implies_result_ind {
/* (If an individual request is accepted THEN the request must produce a result) AND (if an individual request is refused THEN it cannot produce a result)*/
all req :Individual_Request | (req.accepted = True iff req.result != none)  and (req.accepted =False iff req.result = none)}

fact individuals_concerned_by_Anonymised_request {
/* An anonymised request must concern at least 1000 individuals to be accepted.
As Alloy does not allow this type of constraint, we chose to consider that an anonymised request must concern at least 2 individuals
to be accepted*/
(all req: Anonymised_Request | req.accepted=True iff #req.Anonymised_Req_concern >=2) }


fact data_consistency_ind {
/* The data of an individual result is the data of the individual*/
(all req:Individual_Request |req.accepted=True implies (req.result.data=req.Individual_Req_concern.data))}


fact data_consistency_anonymous{
/* The data of a result is the data of the individuals*/
(all req:Anonymised_Request | all ind:req.Anonymised_Req_concern |ind.data in (req.result.data) iff req.accepted = True)}

fact result_proced_by_request{
/* A result cannot exists on his own, it must be produced by a request*/
(all res:Anonymised_Result | some req:Anonymised_Request| res=req.result ) and (all res:Individual_Result | some req:Individual_Request| res=req.result )}

/** ABOUT DATA************/
fact data_unicity{
/* two different individuals cannot have the same data*/ 
all ind, ind' : Individual | no dat:Data | ind != ind' and dat in (ind.data& ind'.data)}

fact data_belong_to_someone{
all dat:Data | some ind:Individual| dat=ind.data
}

/******************************       ASSERTIONS  ***********************************/






/******************************** PREDICATES ************************************/
pred show1{}

pred show2 {#Anonymised_Request=2
					 #Individual_Request=0
					#Third_party = 2
					(some gr:Anonymised_Request | #gr.Anonymised_Req_concern>=2)
					(some gr':Anonymised_Request | #gr'.Anonymised_Req_concern<2)
					(all th:Third_party | #th.Anonym_request_issued = 1)
				 } 

pred show3 {#Anonymised_Request=0
					 #Individual_Request=3
					#Third_party=3
					#Individual=2
					(one req:Individual_Request | req.accepted=False)
					(all th:Third_party | #th.Ind_request_issued = 1)
					(all ind:Individual | #ind.Request_received>=1)
				 } 

--run show2 for 4

run show3 for 6
