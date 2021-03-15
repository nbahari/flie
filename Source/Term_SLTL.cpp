/*
MIT License

Copyright (c) [2019] [Joshua Blickensd�rfer]

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

#include "Header/Term_SLTL.h"

int Term_SLTL::max_Constant = -1;



Term_SLTL::Term_SLTL(std::string & input_Line)
{
	std::stringstream string_stream(input_Line);
	std::string op;
	std::string left;
	std::string right;

	std::getline(string_stream, op, '(');
	oper = op.at(0);
	if (oper == 's') {
		op.erase(op.begin());
		var = std::stoi(op);
	}
	else if (oper == 'c') {
		op.erase(op.begin());
		var = std::stoi(op);
		if (var > max_Constant) max_Constant = var;
	}
	else {

		std::string remaining;
		std::getline(string_stream, remaining);

		int brackets = 0;
		for (unsigned int i = 0; i < remaining.size(); i++) {

			char c = remaining.at(i);

			switch (c) {
			case '(':
				brackets++;
				break;
			case ')':
				brackets--;
				break;
			case ',':
				if (brackets == 0) {
					left = remaining.substr(0, i);
					remaining.erase(remaining.begin(), remaining.begin() + i + 1);
					goto make_Right;
				}
			default:
				break;
			}
		}

	make_Right:

		remaining.erase(remaining.end() - 1);
		right = remaining;


		left_Term = 
		Term_SLTL(left);
		right_Term = new Term_SLTL(right);

	}
}

//computing continuous values btween [0,1] for variables_Y_i_n_t instead of boolean. the any number in the interval is being maped into [0,1]
z3::expr Term_SLTL::compute_Term_cont(std::vector<signal_t>& signals, z3::expr_vector& constants, z3::context& context, bool forall) {

	std::pair<z3::expr,z3::expr> left = left_Term->compute_Term_arithmetic(signals, constants, context);
	std::pair<z3::expr,z3::expr> right = right_Term->compute_Term_arithmetic(signals, constants, context);

	if (forall) { // for all possible pathes

		switch (oper) {
		case '<':
			return z3::min(1,z3::max(0,((right.first-left.first)/(left.second-left.first))));
		case '>':
			return z3::max(0,z3::min(1,((right.first-left.first)/(left.second-left.first))));
		case '=':
		       if ((left.first < left.second) && (right.first < right.second)){    //for cases [a,b] and a<b                            
			    return z3::ite(and((right.firt=left.firts),(right.second=left.second),max(0,((right.first-left.first)/(left.second-left.first))),min(1,((right.first-left.first)/(left.second-left.first))));
			   } else if ((left.first=left.second) && (right.first =right.second)){ //for cased [a,a]
				return z3::ite(left.first=left.second,1,0);
			   }
		case '!':
			return (1-((right.first-left.first)/(left.second-left.first)));
		}

	} else { // for at least one possible path

		switch (oper) {
        case '<':
			return z3::min(1,z3::max(0,((right.first-left.first)/(left.second-left.first))));
		case '>':
			return z3::max(0,z3::min(1,((right.first-left.first)/(left.second-left.first))));
		case '=':
		       if ((left.first < left.second) && (right.first < right.second)){    //for cases [a,b] and a<b                            
			    return z3::ite(and((right.firt=left.firts),(right.second=left.second),max(0,((right.first-left.first)/(left.second-left.first))),min(1,((right.first-left.first)/(left.second-left.first))));
			   } else if ((left.first=left.second) && (right.first =right.second)){ //for cased [a,a]
				return z3::ite(left.first=left.second,1,0);
			   }
		case '!':
			return (1-((right.first-left.first)/(left.second-left.first)));
		}

	}

	throw "Unknown boolean term";
}

std::pair<z3::expr,z3::expr> Term_SLTL::compute_Term_arithmetic(std::vector<signal_t>& signals, z3::expr_vector& constants, z3::context& context) {

	// in a pair, first: lower bound, second: upper bound
	// we assume (lower <= upper) always true
	z3::expr lower(context);
	z3::expr upper(context);

	switch (oper) {
		case 'c':
			lower = constants[var];
			upper = constants[var];
			return std::make_pair(lower,upper);
		case 's':
			lower = context.real_val(signals[var].first.c_str());
			upper = context.real_val(signals[var].second.c_str());
			return std::make_pair(lower,upper);
	}

	std::pair<z3::expr,z3::expr> left = left_Term->compute_Term_arithmetic(signals, constants, context);
	std::pair<z3::expr,z3::expr> right = right_Term->compute_Term_arithmetic(signals, constants, context);

	switch (oper) {
	case '+':
		lower = (left.first + right.first);
		upper = (left.second + right.second);
		return std::make_pair(lower,upper);
	case '-':
		lower = (left.first - right.second);
		upper = (left.second - right.first);
		return std::make_pair(lower,upper);
	case '*': {
		z3::expr l_times_l = left.first * right.first;
		z3::expr l_times_u = left.first * right.second;
		z3::expr u_times_l = left.second * right.first;
		z3::expr u_times_u = left.second * right.second;
		z3::expr l_times_x_min = z3::ite(l_times_l<l_times_u, l_times_l, l_times_u);
		z3::expr l_times_x_max = z3::ite(l_times_l>l_times_u, l_times_l, l_times_u);
		z3::expr u_times_x_min = z3::ite(u_times_l<u_times_u, u_times_l, u_times_u);
		z3::expr u_times_x_max = z3::ite(u_times_l>u_times_u, u_times_l, u_times_u);
		lower = z3::ite(l_times_x_min<u_times_x_min, l_times_x_min, u_times_x_min);
		upper = z3::ite(l_times_x_max>u_times_x_max, l_times_x_max, u_times_x_max);
		return std::make_pair(lower,upper); }
	}

	throw "Unknown arithmetic term";
}


std::string Term_SLTL::print_Term(z3::model& model, z3::expr_vector& constants) {
	std::stringstream result;

	if (oper != 'c' && oper != 's') {
		result << "(";
		result << left_Term->print_Term(model, constants);
		result << oper;
		result << right_Term->print_Term(model, constants);
		result << ")";
	}
	else {


		result << oper;
		result << var;
		if (oper == 'c') {
			result << "(";
			result << model.eval(constants[var]);

			result << ")";
		}
	}

	formula = result.str();
	return formula;
}
