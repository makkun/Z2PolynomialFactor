#include <iostream>
#include <algorithm>
#include <cstring>


using namespace std;


//Overoaded deg for each a[i] and *b
unsigned int deg(const int size, const unsigned int* p)
{
	for (int i = size/16 - 1; i >= 0; i--)
	{
		//print_bits(p[i]);
		if (p[i] != 0)
			for(int j = sizeof(p[i])*8 - 1; j >= 0; j--)
				if (p[i]&(1 << j)) return (i * sizeof(p[0]) * 8) + j;
				
	}
	return 0;
}

unsigned int deg(const int size, const unsigned int p)
{
	for (int i = sizeof(p)*8 - 1; i >= 0; i--) 
		if (p&(1 << i)) return i;
	return 0;
}

//-------------------------------------

void print_expoents(int* expoents, int factor_size)
{
	for (int i = 0; i < factor_size; i++)
	{
		if (i > 0) cout << " ";
		cout << expoents[i];
	}
	cout << endl;
	
}

void print_as_polynomial(unsigned int* a, int size)
{
	for (int i = size*2 - 1; i >= 0; i--)
	{
		if (i < size*2 - 1 and (a[i/32]&(1<<i%32)) and i < deg(size, a))
			printf("+ ");
		if (a[i/32]&(1<<i%32))
		{
			printf("x^%d ", i);
		}
	}
}

void print_bits(unsigned int a){
	int data_size = sizeof(a) * 8;
	for (int i = data_size - 1; i >= 0; i--) printf("%c ", a&(1<<i)?'1':'0');
	printf("\n");

}
void print_bits(unsigned int* a, int size)
{
	for (int i = size/16 - 1; i >= 0; i--)
	{
		print_bits(a[i]);
	}	
}

void assign_value(int size, unsigned int *p, int coordinate, unsigned int value)
{
	if (value) p[coordinate/32] |= (1 << coordinate % 32);
	else p[coordinate/32] &= ~(1 << coordinate % 32);
	
}

bool is_polynomial_equal(unsigned int* p, unsigned int* q, int size)
{
	for (int i = 0; i < size/16; i++)
	{
		if (p[i] != q[i]) return false;
	}
	return true;
}

bool is_polynomial_in_array(unsigned int** array, int array_size, unsigned int* polynomial, int size, int* index)
{
	for (int i = 0; i < array_size; i++)
	{
		if (is_polynomial_equal(array[i], polynomial, size))
		{
			//cout << is_polynomial_equal(array[i], polynomial, size) << endl;
			*index = i;
			return true;
		}
	}
	return false;
	
}

void shift_polynomial_left(int size, unsigned int* p)
{
	for (int i = size/16 - 1; i >= 0; i--)
	{
		p[i] = p[i] << 1;
		if (i > 0 and (p[i - 1] & (1 << 31)))
		{
			assign_value(size, p, i*32, 1); 
		}
	}
}


void print_matrix(int size, int deg_p, unsigned int** matrix, bool no_indent = false, bool brackets = false)
{
	if(brackets) printf("{");
	for (int i = 0; i < deg_p; i++)
	{
		if(brackets) printf("{");
		for (int j = 0; j < deg_p; j++ )
		{
			printf("%c ", matrix[i][j/32]&(1 << (j%32))?'1':'0');
			if (j < deg_p - 1 and brackets)
				printf(",");
		}
		if(brackets) printf("}");
		if(i < deg_p - 1 and brackets) printf(",");
		if (!no_indent and ! brackets) printf("     row:%d", i);
		if (!no_indent) printf("\n");
	}
	if(brackets) printf("}\n");
}

void print_list(int size, int array_size, unsigned int** array, int* expoents)
{

	cout << "Printing Array..." << endl;
	cout << "--------------------------" << endl;

	for (int k = array_size - 1; k >= 0; k--)
	{
		cout << "-----expoent is: " << expoents[k] << " ----------------------------------" << endl;
		print_as_polynomial(array[k], size);
		cout << "--------------------------" << endl;
	}

}

void copy_u_to_v(unsigned int* u, unsigned int* v, int size)
{
	for (int i = size/16 - 1; i >= 0; i--)
		v[i] = u[i];
}

bool compare_polynomials(const unsigned int* u, const unsigned int* v, int size)
{
	if(deg(size, u) < deg(size, v))
	       return true;
	else if(deg(size, v) > deg(size, u))
		return false;
	else
	{
		for(int i = size/16 - 1; i >= 0; i--)
		{
			if (u[i] != v[i])
			{
				//cout << "========" << endl;
				//cout << i << endl;
				//cout << setfill('0') << u[i] << endl;
				//cout << setfill('0') << v[i] << endl;
				//cout << setfill('0') << (u[i]<v[i]) << endl;
				//cout << "=========="<< endl;	
				return (u[i] < v[i]);
			}
		}
	}
	return true;
}

unsigned int** get_pseudodivision_quotient_and_residue(unsigned int* u, unsigned int* v, int size) //Uses pseudodivision to calculate a division residue: l(v)^(m-n-1)u(x) = q(x)v(x) + r(x) with m and n deg of u and v
{
	int m = deg(size, u);
	int n = deg(size, v);
	//printf("%d, %d \n", m,n);
	int array_size = size/16;
	unsigned int* q = new unsigned int[array_size];
	unsigned int* copy_u = new unsigned int[array_size];

	unsigned int** q_and_r = new unsigned int*[2]; 
	
	copy_u_to_v(u, copy_u, size);

	for (int k = m-n; k >= 0; k--)
	{
		//printf("k = %d\n", k);
		//q[k/32] ^= ((u[(n+k)/32]&(1 << (n+k)%32))&(v[n/32]&(1 << n%32)))&(1 << k%32); This equation is wrong, but gives a good idea on qhat is going to happen
		unsigned int u_n_k = copy_u[(n+k)/32]&(1 << (n+k)%32)?1:0;
		//printf("q_%d = %d and %d \n", k, u_n_k, v_n);
		if (u_n_k) q[k/32] |= (1 << k % 32);
		else q[array_size - k/32] &= ~(1 << k%32);

		for (int j = n+k-1; j>= 0; j--)
		{
			//printf("j = %d\n", j);
			u_n_k = copy_u[(n+k)/32]&(1 << (n+k)%32)?1:0;
			unsigned int u_j = copy_u[j/32]&(1 << j%32)?1:0;
			unsigned int v_j_k = v[(j-k)/32]&(1 << (j-k)%32)?1:0;
			v_j_k = ( j >= k )?v_j_k:0;
			//printf("u_%d = %d and %d xor %d and %d\n", j, v_n, u_j, u_n_k, v_j_k);
			if ((u_j) ^ (u_n_k & v_j_k)) copy_u[j/32] |= (1 << j% 32);
			else copy_u[j/32] &= ~(1 << j % 32);
		}
	}
	for (int i = m; i>=n; i--) copy_u[i/32] &= ~(1 << i%32); //The algorithm returns u(x) where the n-1 first coefficients are euqal to r(x)
	q_and_r[0] = q;
	q_and_r[1] = copy_u;
//	print_bits(copy_u[0]);
//	print_bits(copy_u[1]);
	return q_and_r;
}

unsigned int* diff_polynomial(unsigned int* f, int size){
	unsigned int f_clearer  = (1 << (sizeof(int)*8 - 1))/3;	 //Generating a number that, in binary, is 1 on odd index and 0 on even index
	f_clearer = (f_clearer - 1)<<1;
	unsigned int* df = new unsigned int[size/16];
//	cout << "operator is: "<< endl;
//	print_bits(f_clearer);
	for (int i = size/16 - 1; i >= 0; i--)
	{
		if (f[i] != 0)
		{
			df[i] = (f[i]&f_clearer) >> 1;
		}
	}
//	print_bits(p);
//	print_bits(diff_p);
	return df;
}

bool is_polynomial_zero(unsigned int* u, int size)
{
	for (int i = size/16 - 1; i >= 0; i--) 
		if (u[i]) return false;
	return true;
}

bool is_polynomial_unity(unsigned int* u, int size)
{
	for (int i = size/16; i >= 0; i--)
	{
		if (i > 0)
		{
			if(u[i])
				return false;
		}
		else
		{
			return (u[i] == 1);
		}
	}
	return false;
}

unsigned int* multiply_polynomial(unsigned int* u, unsigned int* v, int size)
{
	int deg_u = deg(size, u);
	int deg_v = deg(size, v);
	int m_size = size/16;
	unsigned int* m = new unsigned int[m_size];
	for (int k = 0; k < m_size; k++)
		m[k] = 0;
	for (int i = 0; i <= deg_u; i++)
		for (int j = 0; j <= deg_v; j++)
		{
			m[(i + j)/32] ^= (((u[i/32] >> (i % 32)) & (v[j/32] >> (j % 32))) & 1) << ((i + j) % 32);
		}
	return m;
}

unsigned int* gcd(unsigned int* u, unsigned int* v, int size)
{
	bool finish = false;
	unsigned int* a = new unsigned int[size/2];
	copy_u_to_v(u, a, size);
	unsigned int* b = new unsigned int[size/2];
	copy_u_to_v(v, b, size);
	unsigned int* r = new unsigned int[size/2];

	if (deg(size, u) > deg(size, v))
	{
		copy_u_to_v(u, a, size);
		copy_u_to_v(v, b, size);
	}
	else
	{
		copy_u_to_v(u, b, size);
		copy_u_to_v(v, a, size);
	}

	while(not finish)
	{
		copy_u_to_v(get_pseudodivision_quotient_and_residue(a, b, size)[1], r, size);
		//cout << "---" << endl;
		//print_bits(r, size);
		//cout << "---" << endl;
		//printf("%d \n", deg(32, r));
		if (deg(size, r) == 0)
			finish = true;
		else 
		{
			copy_u_to_v(b, a, size); //Its inverted we are copying u to v
			copy_u_to_v(r, b, size);
		}
//		cout<< "----r"<< endl;
//		print_bits(r, size);
//		cout << "-----v"<< endl;
//		print_bits(copy_v, size);
//		cout << "Finish Cicle" << endl;
//		printf("%d \n", deg(32, r));
//		cout << "------" << endl;
	}


	if (r[0] == 0)
		return b;
	else
	{
		r[0] = 1;
		return r;
	}

}

unsigned int* polynomial_sqrt(unsigned int* u, int size, int* k) //Given u(x) = Sum(a_n*x^n) where if n is even a_n != 0 and a_n = 0 otherwise, It finds v(x) wich u(x) = v(x^2k)
{
	unsigned int * copy_u = new unsigned int[size/16];
	unsigned int * sqrt = new unsigned int[size/16];
	int deg_u = deg(size, u);
	copy_u_to_v(u, copy_u, size);
	//cout << *k << endl;
	for (int i = deg_u; i >= 0; i--)
	{
		if (copy_u[i/32]&(1 << i % 32))
			sqrt[i/64] |=  (1 << ((i/2) % 32));
	}
	*k *= 2;
	if (is_polynomial_zero(diff_polynomial(sqrt,size), size))
		return polynomial_sqrt(sqrt, size, k);
	else
		return sqrt;
}

unsigned int** generate_matrix_Q_minus_I(unsigned int * p,  int size)
{
	int deg_p = deg(size, p);
	unsigned int** matrix_Q_minus_I = new unsigned int* [deg_p];
	unsigned int* a_k_minus_1 = new unsigned int[size/16];
	unsigned int* a_k;
	for (int k = 0; k <=(deg_p - 1)*2; k++)
	{
		a_k = new unsigned int[size/16];	
		if (k < deg_p)
		{
			assign_value(size, a_k, k, 1);	
		}
		else
		{
			unsigned int n_minus_1_coeff = (a_k_minus_1[(deg_p - 1)/32]&(1 << (deg_p - 1)%32))?(0-1):0; //Extracting the a_(k-1, n-1) coefficient
			if(a_k_minus_1[(deg_p - 1)/32] & (1 << (deg_p - 1)%32)) assign_value(size, a_k_minus_1, deg_p - 1, 0); //zeroing the a_(k-1, n-1) coefficient
			//print_bits(a_k_minus_1, size);
			shift_polynomial_left(size, a_k_minus_1);
			for (int j = (deg_p - 1)/32; j >= 0; j--)
				a_k[j] = a_k_minus_1[j] ^ (n_minus_1_coeff & p[j]);

		}	
		//cout << k << " row is" << endl;
		//print_bits(a_k, size);
		copy_u_to_v(a_k, a_k_minus_1, size); //We can add a conditional to copy only when k >= deg_p - 1

		if (k%2==0)
		{
			a_k[k/64] ^= (1 << ((k/2) % 32));
			matrix_Q_minus_I[k/2] = new unsigned int [size/16];
			copy_u_to_v(a_k, matrix_Q_minus_I[k/2], size);
		}

		

	}
	//print_matrix(size, deg_p, matrix_Q_minus_I);

	return matrix_Q_minus_I;
}

void sum_column_j_to_column_i(unsigned int** M, int matrix_size, int j, int i, int size)
{
	for(int k = 0; k < matrix_size; k++)
	{
		int value_i = M[k][i/32]&(1 << i%32)?1:0;
		int value_j = M[k][j/32]&(1 << j%32)?1:0;
		assign_value(size, M[k], i, value_i^value_j);
	}
}

bool scan_row_for_dependence( unsigned int** M, int matrix_size, int size, int k, int* c )
{
	bool r_value = false;
	for (int j = 0; j < matrix_size; j++)
	{
		if ((M[k][j/32]&(1 << j%32)) != 0 and c[j] < 0)
		{
			for(int i = 0; i < matrix_size; i++)
			{
				if (i != j and (M[k][i/32]&(1 << i%32)) != 0)
				{
					sum_column_j_to_column_i(M, matrix_size, j, i, size);
				}
			}
			c[j] = k;
			//cout << "Step k = " << k <<", c ["<< j << "] = "<< c[j] << endl;
			//print_matrix(size, matrix_size, M);
			//cout << "----------------------------" << endl;
			return true;
		}
	}
	return r_value;
}

void update_factors_and_expoents(unsigned int** factors, int* expoents, int* factor_size, int size, unsigned int* f, int p_k)
{
	int index;
	if(is_polynomial_in_array(factors, *factor_size, f, size, &index))
		expoents[index] += 1*p_k;
	else
	{
		factors[*factor_size] = new unsigned int[size/16];
		copy_u_to_v(f, factors[*factor_size], size);
		expoents[*factor_size] += 1*p_k;
		*factor_size += 1;
	}
}

unsigned int** find_ker_basis(unsigned int** M, int matrix_size, int size, int* r)
{
	unsigned int** basis = new unsigned int*[size*2];
	int* c = new int[matrix_size];
	int ker_dim = 0;
	for (int t = 0; t < matrix_size; t++)
		c[t] = -1;

	for (int k = 0; k < matrix_size; k++)
	{
		if (!scan_row_for_dependence(M , matrix_size, size, k ,c))
		{
			unsigned int* v = new unsigned int [size/16];
			for (int j = 0; j < matrix_size; j++)// To make more general replace 32 with matrix_size
			{
				int* index = std::find(c, c + matrix_size, j);
				if (index != c + matrix_size)
				{
					assign_value(size, v, j, (M[k][(index - c)/32]&(1<<(index - c)%32))?1:0);
				}

				else if(j == k)
				{
					assign_value(size, v, j, 1);
				}
				else
				{
					assign_value(size, v, j, 0);
				}
			}
			//print_as_polynomial(v, size);
			basis[ker_dim] = v;
			ker_dim++;
		}
	}

	//cout << ker_dim << endl;
		
	//cout << "Simplified Matrix" << endl;
	//print_matrix(size, matrix_size, M);
	//cout << "---------------------" << endl;
	*r = ker_dim;

	return basis;
}

void print_list_of_polynomials(unsigned int** l_p, int size, int list_size)
{
	cout << "The list is:" << endl;
	for (int i = 0; i < list_size; i++)
	{
		print_as_polynomial(l_p[i], size);
		cout << "------------------------------------------" << endl;
	}
	cout << "=-=-=-=-=-=-=-=-=-=-=-=-=-=-==-=-=-=-=-=-=-=-=" << endl;
}

void find_factors_of_f_with_basis(unsigned int** basis, unsigned int* f, int ker_dim, int size, unsigned int** factors, int* expoents, int p_k, int* factor_size)
{
	unsigned int** candidates_w = new unsigned int* [ker_dim];
	unsigned int** collected_gcds = new unsigned int* [ker_dim];
	for (int k = 0; k < ker_dim; k++)
	{
		candidates_w[k] = new unsigned int[size/16];
		collected_gcds[k] = new unsigned int[size/16];
	}

	copy_u_to_v(f, candidates_w[0], size);
	int collected_gcds_size = 0;
	int candidates_w_size = 1;

	for (int i = 1; i < ker_dim; i++)
	{
		//cout << "ITERATION i = " << i << endl;
		unsigned int* v = new unsigned int[size/16];
		for (int j = 0; j < candidates_w_size; j++)
		{
			copy_u_to_v(basis[i], v, size);
			for (int d = 0; d < 2; d++)
			{
				assign_value(size, v, 0, (v[0]^d)&1);
				unsigned int* g = gcd(v, candidates_w[j], size);
				int index;
				if (!is_polynomial_unity(g, size))
				{
					if (!is_polynomial_in_array(collected_gcds, collected_gcds_size, g, size, & index))
					{
						copy_u_to_v(g, collected_gcds[collected_gcds_size], size);
						collected_gcds_size += 1;
					}
				}
				else //if(i > 1)
				{
					if (!is_polynomial_in_array(collected_gcds, collected_gcds_size, candidates_w[j], size, & index))
					{
						copy_u_to_v(candidates_w[j], collected_gcds[collected_gcds_size], size);
						collected_gcds_size += 1;
					}
				}
				//cout << "=================gcd======================" << endl;
				//print_as_polynomial(v, size);
				//print_as_polynomial(candidates_w[j], size);
				//cout << "------------------------------------------" << endl;
				//print_as_polynomial(g, size);
				//cout << "------------------------------------------" << endl;
				if (collected_gcds_size == ker_dim) 
				{
					for (int s = 0; s < ker_dim; s++)
					{
						//cout << "p_k is " << p_k << endl;
						//print_list_of_polynomials(collected_gcds, size, collected_gcds_size);
						update_factors_and_expoents(factors, expoents, factor_size, size, collected_gcds[s], p_k);
					}
					//factors <-- collected_gcds
					return;
				}
			}
		}
		//print_list_of_polynomials(collected_gcds, size, collected_gcds_size);
		candidates_w_size = collected_gcds_size;
		collected_gcds_size = 0;
		for (int k = 0; k < candidates_w_size; k++)
			copy_u_to_v(collected_gcds[k], candidates_w[k], size);
	}


	return;
}


void factoring_polynomial(unsigned int* f, int size, unsigned int** factors, int* factor_size, int* expoents, int p_k)
{
	//cout << "p_k is: " << p_k << endl;
	unsigned int* df = diff_polynomial(f, size);
	unsigned int* g = gcd(f, df, size);
	//cout << "Your f is" << endl;
	//print_as_polynomial(f, size);
	//cout << "Your df is" << endl;
	//print_bits(df, size);
	//cout << "gcd(f, df) is:" << endl;
	//print_bits(g, size);

	if (deg(size, f) == 1)
	{
		update_factors_and_expoents(factors, expoents, factor_size, size, f, p_k);
		return;
	}

	else if (is_polynomial_zero(df, size))
	{
		//cout << "------------------------------------------------" << endl;
		//cout << "f is of the form a_nx^n where a_n != only if p|n"<< endl;
		//cout << "------------------------------------------------" << endl;
		unsigned int* sqrt = new unsigned int[size/16];
		sqrt = polynomial_sqrt(f, size, &p_k);
		factoring_polynomial(sqrt, size, factors, factor_size, expoents, p_k);
		return ;
	}
	else if (is_polynomial_unity(g, size))
	{
		//cout << "------------------------------------------------" << endl;
		//cout << "f is already square-free"<< endl;
		//cout << "------------------------------------------------" << endl;
		int ker_dim = 0;
		unsigned int** basis = find_ker_basis(generate_matrix_Q_minus_I(f, size), deg(size, f), size, &ker_dim);
		if (ker_dim == 1)
		{
			//cout << "Ker Dim is one!!!!!" << endl;
			update_factors_and_expoents(factors, expoents, factor_size, size, f, p_k);

		}
		else
		{
			//cout << "Factors of: " << endl;
			//print_as_polynomial(f, size);
			//cout << "---------------------------->" << endl;
			find_factors_of_f_with_basis(basis, f, ker_dim, size, factors, expoents, p_k, factor_size);
			//cout << "--------------------"<< endl;
		}
		
		return;
	}
	else
	{
		unsigned int* q = get_pseudodivision_quotient_and_residue(f, g, size)[0];
		//cout << "------------------------------------------------" << endl;
		//cout << "f' is a proper factor of f, f/g is:" << endl;
		//cout << "------------------------------------------------" << endl;
		//cout << "And p_k is: " << p_k << endl;
		factoring_polynomial(g, size, factors, factor_size, expoents, p_k);
		factoring_polynomial(q, size, factors, factor_size, expoents, p_k);
		return;
	}
}

int calculate_total_degree_of_multiplication(unsigned int** factor, int* expoents, int* max_expoents, int size, int factor_size)
{
	int return_value = 0;
	for(int i = 0; i < factor_size; i++)
	{
		return_value += deg(size, factor[i]) * expoents[i];
	}
	return return_value;
}

unsigned int* build_polynomial_from_factors(unsigned int** factor, int* expoents, int size, int factor_size)
{
	unsigned int* p = new unsigned int[size/16];
	p[0] = 1;

	for(int i = 0; i < factor_size; i++)
	{
		for(int k = 0; k < expoents[i]; k++)
		{
			copy_u_to_v(multiply_polynomial(p, factor[i], size), p, size);
		}
	}

	return p;
}

bool tick_expoents(int* expoents, int* max_expoents, int factor_size)
{
	if (expoents[0] == max_expoents[0])
	{
		expoents[0] = 0;
		bool ripple = true;
		int i = 1;
		while (ripple and i < factor_size)
		{
			if (expoents[i] == max_expoents[i])
			{
				expoents[i] = 0;
			}
			else
			{
				ripple = false;
				expoents[i] += 1;
			}
			i++;
		}
		if (factor_size == i and ripple)
			return false;
	}
	else
		expoents[0] += 1;

	return true;
}

unsigned int** get_all_possible_inputs(unsigned int** factors, int* max_expoents, int factor_size, int size, unsigned int* f, int* e_possibilities_size)
{

	int* copy_expoents = new int[factor_size];
	copy_expoents[0] = -1;
	unsigned int** copy_factors = new unsigned int* [factor_size];
	int number_of_splits = 1;
	for (int i = 0; i < factor_size; i++)
	{
		number_of_splits *= (max_expoents[i] + 1);
		copy_factors[i] = new unsigned int[size/16];
		copy_u_to_v(factors[i], copy_factors[i], size);
	}

	unsigned int** possibilities = new unsigned int* [number_of_splits<<(size/32 - 1)];
	int possibilities_size = 0;

	while(tick_expoents(copy_expoents, max_expoents, factor_size))
	{
		int deg_split = calculate_total_degree_of_multiplication(factors, copy_expoents, max_expoents, size, factor_size);
		if (deg_split < size and (deg(size, f) - deg_split) < size)
		{
			unsigned int* possible_input_a = build_polynomial_from_factors(factors, copy_expoents, size, factor_size);
			unsigned int* possible_input_b = get_pseudodivision_quotient_and_residue(f, possible_input_a, size)[0];

			std::reverse(possible_input_a, possible_input_a + size/32); // We were using endian notation (a_n, a_n-1, ..., a_1, a_0) so just reverse it to (a_0, a_1, ..., a_n)
			std::reverse(possible_input_b, possible_input_b + size/32); //For the final half the polynomial is zero, on both

			//cout << "=============================================" << endl;
			//print_as_polynomial(possible_input_a, size);
			//cout << "---------------------------------------------" << endl;
			//print_as_polynomial(possible_input_b, size);
			//cout << "=============================================" << endl;
			possibilities[possibilities_size] = new unsigned int[size/16];
			for (int i = 0; i < size/32; i++)
			{
				possibilities[possibilities_size][i] = possible_input_a[i];
				possibilities[possibilities_size][i + size/32] = possible_input_b[i];
			}
			possibilities_size += 1;
		}
	}

	*e_possibilities_size = possibilities_size;
	return possibilities;
}

class polynomials_comparator{
	private:
		int size;
		unsigned int** list;
	public:
		polynomials_comparator(unsigned int** array, int v_size){list = array; size = v_size;}
		bool operator()(const unsigned int* a, const unsigned int* b) const {return compare_polynomials(a, b, size);}
};

unsigned int* string_to_hex(string line, int size)
{
    unsigned int* b = new unsigned int[size/16];
    string c = "";
    int iterator = 0;
    for(int i = 0; i <= line.length(); i++)
    {
        if (!(line[i] == ' ') and i < line.length())
            c += line[i];
        else
        {
            b[iterator] = stol(c, nullptr, 16);
            c = "";
            iterator += 1;
        }
    }
    return b;
}

void vector_to_polynomial(int* vector, unsigned int*p, int degree, int size)
{
	for (int i = 0; i <= degree; ++i)
	{
		assign_value(size, p, i, vector[i]%2);
	}
}


int main(){
	cout << "Enter the degree of the polynomial:" << endl;
	cout << ">> ";
	unsigned int degree;
	cin >> degree;
	cout << endl;
	int* coeff = new int[degree+1];
	cout << "Write all coefficients, startingo from the x^0:" << endl;
	for(unsigned int i = 0; i< degree+1; ++i)
	{
		cout << "Enter the "<< i << "th coefficient:" << endl;
		cout << ">> ";
		cin >> coeff[i];
		cout << endl;
	}

	int size = 64;
	while(size <= degree)
	{
		size *= 2;
	}

	unsigned int* p = new unsigned int[size/32];
	vector_to_polynomial(coeff, p, degree, size);

	cout << "Your Polynomial is:" << endl;
	cout << ">>";
	print_as_polynomial(p, size/2);
	cout << endl;

	unsigned int** factors = new unsigned int* [size];
	int* expoents = new int[size];
	int factors_size = 0;
	factoring_polynomial(p, size/2, factors, &factors_size, expoents, 1);

	cout << "His Factorization is" << endl;

	for (int i = 0; i < factors_size; ++i)
	{
		cout << "(";
		print_as_polynomial(factors[i], size);
		cout << ")^" << expoents[i] << " ";
	}

	cout << endl;

}
