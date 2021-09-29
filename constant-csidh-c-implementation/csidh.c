#include <string.h>
#include <assert.h>

#include "csidh.h"
#include "rng.h"

const unsigned primes[num_primes] = {    349, 347, 337, 331, 317, 313, 311,
307, 293, 283, 281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229,
227, 223, 211, 199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151,
149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73,
71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3,
587, 373, 367, 359, 353 };

const u512 four_sqrt_p = { { 0x85e2579c786882cf, 0x4e3433657e18da95,
		0x850ae5507965a0b3, 0xa15bc4e676475964, } };

const public_key base = { 0 }; /* A = 0 */

/* get priv[pos] in constant time  */
uint32_t lookup(size_t pos, int8_t const *priv)
{
	int b;
	int8_t r = priv[0];
	for(size_t i=1;i<num_primes;i++)
	{
		b = isequal(i, pos);
		//ISEQUAL(i, pos, b);
		//b = (uint8_t)(1-((-(i ^ pos)) >> 31));
		cmov(&r, &priv[i], b);
		//CMOV(&r, &priv[i], b);
	}
	return r;
}

/* check if a and b are equal in constant time  */
uint32_t isequal(uint32_t a, uint32_t b)
{
	//size_t i;
	uint32_t r = 0;
	unsigned char *ta = (unsigned char *)&a;
	unsigned char *tb = (unsigned char *)&b;
	r = (ta[0] ^ tb[0]) | (ta[1] ^ tb[1]) | (ta[2] ^ tb[2]) |  (ta[3] ^ tb[3]);
	r = (-r);
	r = r >> 31;
	return (int)(1-r);
}


/* decision bit b has to be either 0 or 1 */
void cmov(int8_t *r, const int8_t *a, uint32_t b)
{
	uint32_t t;
	b = -b; /* Now b is either 0 or 0xffffffff */
	t = (*r ^ *a) & b;
	*r ^= t;
}


void csidh_private(private_key *priv, const int8_t *max_exponent) {
	memset(&priv->e, 0, sizeof(priv->e));
	for (size_t i = 0; i < num_primes;) {
		int8_t buf[64];
		randombytes(buf, sizeof(buf));
		for (size_t j = 0; j < sizeof(buf); ++j) {
			if (buf[j] <= max_exponent[i] && buf[j] >= 0) {
				priv->e[i] = lookup(j, buf);
				if (++i >= num_primes)
					break;
			}
		}
	}
}

/* compute [(p+1)/l] P for all l in our list of primes. */
/* divide and conquer is much faster than doing it naively,
 * but uses more memory. */
static void cofactor_multiples(proj *P, const proj *A, size_t lower,
		size_t upper) {
	assert(lower < upper);

	if (upper - lower == 1)
		return;

	size_t mid = lower + (upper - lower + 1) / 2;

	u512 cl = u512_1, cu = u512_1;
	for (size_t i = lower; i < mid; ++i)
		u512_mul3_64(&cu, &cu, primes[i]);
	for (size_t i = mid; i < upper; ++i)
		u512_mul3_64(&cl, &cl, primes[i]);

	xMUL(&P[mid], A, &P[lower], &cu);
	xMUL(&P[lower], A, &P[lower], &cl);

	cofactor_multiples(P, A, lower, mid);
	cofactor_multiples(P, A, mid, upper);
}

/* never accepts invalid keys. */
bool validate(public_key const *in) {
	const proj A = { in->A, fp_1 };

	do {

		proj P[num_primes];
		fp_random(&P->x);
		P->z = fp_1;

		/* maximal 2-power in p+1 */
		xDBL(P, &A, P);
		xDBL(P, &A, P);

		cofactor_multiples(P, &A, 0, num_primes);

		u512 order = u512_1;

		for (size_t i = num_primes - 1; i < num_primes; --i) {

			/* we only gain information if [(p+1)/l] P is non-zero */
			if (memcmp(&P[i].z, &fp_0, sizeof(fp))) {

				u512 tmp;
				u512_set(&tmp, primes[i]);
				xMUL(&P[i], &A, &P[i], &tmp);

				if (memcmp(&P[i].z, &fp_0, sizeof(fp)))
					/* P does not have order dividing p+1. */
					return false;

				u512_mul3_64(&order, &order, primes[i]);

				if (u512_sub3(&tmp, &four_sqrt_p, &order)) /* returns borrow */
					/* order > 4 sqrt(p), hence definitely supersingular */
					return true;
			}
		}

		/* P didn't have big enough order to prove supersingularity. */
	} while (1);
}

/* compute x^3 + Ax^2 + x */
static void montgomery_rhs(fp *rhs, fp const *A, fp const *x) {
	fp tmp;
	*rhs = *x;
	fp_sq1(rhs);
	fp_mul3(&tmp, A, x);
	fp_add2(rhs, &tmp);
	fp_add2(rhs, &fp_1);
	fp_mul2(rhs, x);
}


/* generates a curve point with suitable field of definition for y-coordinate */
void elligator(fp * x, const fp *A, bool sign, uint8_t index) {

	fp legendre_symbol;
	// v = A/(u^2 − 1)
	fp_set(x, 0);
	fp_add2(x, &invs_[index]);
	fp_mul2(x, A);
	// Compute the Legendre symbol
	montgomery_rhs(&legendre_symbol, A, x);
	// Compute x as v if e = s
	if(fp_issquare(&legendre_symbol)!=sign){
		// otherwise − v − A
		fp_add2(x, A);
		fp_sub3(x, &fp_0, x);

	}

}

/* constant-time. */
void action(public_key *out, public_key const *in, private_key const *priv,
		uint8_t num_batches, int8_t const *max_exponent, unsigned int const num_isogenies, uint8_t const my) {

	//factors k for different batches, where
	// k[0] = 4*347*337*331*317*311*307*293*283*277*271*269*263*251*241*239*233*227*223*211*199*
	//		  193*191*181*179*167*163*157*151*139*137*131*127*109*107*103*101*89*83*79*73*67*61*
	//		  59*53*43*41*37*31*23*19*17*13*7*5*3*587*367*359*353
    // k[1] = 4*349*337*331*317*313*307*293*283*281*271*269*263*257*241*239*233*229*223*211*199*
	//		  197*191*181*179*173*163*157*151*149*137*131*127*113*107*103*101*97*83*79*73*71*61*
	//		  59*53*47*41*37*31*29*19*17*13*11*5*3*587*373*359*353
	// k[2] = 4*349*347*331*317*313*311*293*283*281*277*269*263*257*251*239*233*229*227*211*199*
	//	      197*193*181*179*173*167*157*151*149*139*131*127*113*109*103*101*97*89*79*73*71*67*
	//		  59*53*47*43*37*31*29*23*17*13*11*7*3*587*373*367*353
	// k[3] = 4*349*347*337*317*313*311*307*283*281*277*271*263*257*251*241*233*229*227*223*199*
	//        197*193*191*179*173*167*163*151*149*139*137*127*113*109*107*101*97*89*83*73*71*67*
	//		  61*53*47*43*41*31*29*23*19*13*11*7*5*587*373*367*359
	// k[4] = 4*349*347*337*331*313*311*307*293*281*277*271*269*257*251*241*239*229*227*223*211*
	//        197*193*191*181*173*167*163*157*149*139*137*131*113*109*107*103*97*89*83*79*71*67*
	//		  61*59*47*43*41*37*29*23*19*17*11*7*5*3*373*367*359*353
	u512 k[5] = {{ .c ={0xf8b02e1700e5ee44, 0xf113c71293a701b4, 0x5fd885e12f150737, 0x16bee0bbd716609d, 0xbd430c7bfb2b427a, 0xfe73b882c492385b, 0x33aac5, 0x0} },
			{ .c ={0xcc61abcfc937ab44, 0x68017a4fbca98e6, 0xb12a83d63b6d445e, 0x529b3cbc63a7b0d, 0x17202f85bd5805a, 0xc016cb54ebcba550, 0xa3b3ad, 0x0} },
			{ .c ={0x577ac7ea0ad4df54, 0xf7fe384bdffcd347, 0x3f8f42993c859a18, 0x80941dcb4ab8587b, 0x4f161b75c99c7f42, 0x67ec629ef79ae535, 0x1a7b5b5, 0x0} },
			{ .c ={0x3e6be99cc0eb105c, 0x93274e02ae2375f, 0xe7ae846eaa92dbd7, 0xd2bb6f974f14003e, 0x2d60e4c0479db07f, 0xde09242d07f74906, 0x5251c74, 0x0} },
			{ .c = {0x8aa000e50dd9c3ac, 0xbc4279114b16bb9c, 0x3e8c74248a72149f, 0x06a02aa8ba62b16c, 0x99fe9a8a6931bc52, 0x445697c5f857e177, 0x00000000173650e4, 0x0000000000000000}}};

	u512 p_order = { .c = {0x24403b2c196b9323, 0x8a8759a31723c208, 0xb4a93a543937992b, 0xcdd1f791dc7eb773, 0xff470bd36fd7823b, 0xfbcf1fc39d553409, 0x9478a78dd697be5c, 0x0ed9b5fb0f251816}};

	int8_t ec = 0, m = 0;
	uint8_t count = 0;
	uint8_t elligator_index = 0;
	uint8_t last_iso[5], bc;
	proj P, K;
	u512 cof;
	bool finished[num_primes] = {0};
	int8_t e[num_primes] = {0};
	int8_t counter[num_primes] = {0};
	unsigned int isog_counter = 0;

	//index for skipping point evaluations
	last_iso[0] = 70;
	last_iso[1] = 71;
	last_iso[2] = 72;
	last_iso[3] = 73;
	last_iso[4] = 69;

	memcpy(e, priv->e, sizeof(priv->e));

	memcpy(counter, max_exponent, sizeof(counter));

	proj A = { in->A, fp_1 };

	while (isog_counter < num_isogenies) {
		m = (m + 1) % num_batches;
		
		if(count == my*num_batches) {  //merge the batches after my rounds
			m = 0;
			last_iso[0] = 73;    //doesn't skip point evaluations anymore after merging batches
			u512_set(&k[m], 4);  //recompute factor k
			num_batches = 1;

			// no need for constant-time, depends only on randomness
			for (uint8_t i = 0; i < num_primes; i++) {
				if(counter[i]==0) {
					u512_mul3_64(&k[m], &k[m], primes[i]);
				}
			}
		}

		assert(!memcmp(&A.z, &fp_1, sizeof(fp)));

		if(memcmp(&A.x, &fp_0, sizeof(fp))) {
			elligator(&P.x, &A.x, true, elligator_index);
			elligator_index = (elligator_index + 1)%9;
			P.z = fp_1;
		} else {
			fp_enc(&P.x, &p_order); // point of full order on E_a with a=0
			P.z = fp_1;
		}

		xMUL(&P, &A, &P, &k[m]);

		for (uint8_t i = m; i < num_primes; i = i + num_batches) {
			if(finished[i] == true) {  //depends only on randomness
				continue;
			} else {
				cof = u512_1;
				for (uint8_t j = i + num_batches; j < num_primes; j = j + num_batches) {
					if (finished[j] == false)  //depends only on randomness
						u512_mul3_64(&cof, &cof, primes[j]);
				}
				xMUL(&K, &A, &P, &cof);

				ec = lookup(i, e);  //check in constant-time if normal or dummy isogeny must be computed
				bc = isequal(ec, 0);


				if (memcmp(&K.z, &fp_0, sizeof(fp))) {  //depends only on randomness

						if (i == last_iso[m])
							lastxISOG(&A, &P, &K, primes[i], bc);
						else
							xISOG(&A, &P, &K, primes[i], bc);

						e[i] = ec - (1 ^ bc);
						counter[i] = counter[i] - 1;
						isog_counter = isog_counter + 1;



				}

			}


			if(counter[i]==0) {   //depends only on randomness
				finished[i] = true;
				u512_mul3_64(&k[m], &k[m], primes[i]);
			}
		}




		fp_inv(&A.z);
		fp_mul2(&A.x, &A.z);
		A.z = fp_1;
		count = count + 1;

	}

	out->A = A.x;

}


/* includes public-key validation. */
bool csidh(public_key *out, public_key const *in, private_key const *priv,
		uint8_t const num_batches, int8_t const *max_exponent, unsigned int const num_isogenies, uint8_t const my) {
	if (!validate(in)) {
		fp_random(&out->A);
		return false;
	}
	action(out, in, priv, num_batches, max_exponent, num_isogenies, my);

	return true;
}


