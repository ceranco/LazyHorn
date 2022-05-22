#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <chrono>
#include <future>
#include "z3++.h"
#include "lazy_horn.h"
#include "Global.h"
#include "Stats.h"

using namespace z3;
using namespace LazyHorn;
using namespace std;

#include "boost/program_options.hpp"
namespace po = boost::program_options;

std::string parseCmdLine(int argc, char **argv) {
    po::options_description generic("Options");
    generic.add_options()("help", "produce help message")(
        "print-params", "print current parameters")(
        "alg", po::value<unsigned>(&gParams.alg)->default_value(0),
        "Solver: 0 - Z3, 1 - IH")(
        "verbose,v", po::value<unsigned>(&gParams.verbosity)->default_value(0),
        "Verbosity level: 0 means silent")("version", "Print version string")(
        "cover_strat",po::value<unsigned>(&gParams.cover_update_strat)->default_value(0))(
        "random_seed", po::value<unsigned>(&gParams.random_seed)->default_value(0),
        "Random seed to be used by SMT solver")(
        "addition_strat",po::value<unsigned>(&gParams.clause_addition_strat)->default_value(0),
        "0 ssp, 1 loop-free-ssp, 2 top-down-ssp")(
        "array_theory",po::value<unsigned>(&gParams.array_theory)->default_value(0),
        "0 no, 1 yes")(
        "context_strat",po::value<unsigned>(&gParams.context_strat)->default_value(0),
        "0 same, 1 fresh");

    po::options_description hidden("Hidden options");
    hidden.add_options()("input-file", po::value<string>(), "input file");

    po::options_description cmdline;
    cmdline.add(generic).add(hidden);

    po::positional_options_description p;
    p.add("input-file", -1);

    try {
        po::variables_map vm;
        po::store(po::command_line_parser(argc, argv)
        .options(cmdline)
        .positional(p)
        .run(),
        vm);
        po::notify(vm);

        if (vm.count("help")) {
            cout << generic << "\n";
            std::exit(1);
        }

        if (vm.count("print-params")) {
            cout << gParams << "\n";
            std::exit(1);
        }
        if (vm.count("version")) {
            cout << "Ih (" << 0 << ")\n";
            if (!vm.count("input-file")) std::exit(1);
        }

        if (!vm.count("input-file")) {
            cout << "Error: No SMT file specified\n";
            std::exit(1);
        }

        gParams.fName = vm["input-file"].as<string>();

        VERBOSE(2, vout() << gParams << "\n";);

        return gParams.fName;
    } catch (std::exception &e) {
        cout << "Error: " << e.what() << "\n";
        std::exit(1);
    }
}

void test_query(string fileName) {
    IH_MEASURE_FN;
    
    lazy_horn ih(fileName.c_str(), gParams.verbosity);

    check_result res = ih.query();
    if (res == z3::sat) {
        Stats::set("Result", "SAT");
    } else if (res == z3::unsat) {
        Stats::set("Result", "UNSAT");
    } else {
        Stats::set("Result", "UNKNOWN");
    }

    Stats::uset("Iters", ih.get_num_of_iterations());
    Stats::uset("LSIter", ih.get_last_significant_iteration());
    Stats::uset("Asserts", ih.get_num_of_assertions());
    Stats::uset("NeededAsserts", ih.get_num_of_needed_assertions());

    if (gParams.verbosity > 1) {
        ih_expr_vec covers = ih.get_covers();
        func_decl_vec node_to_decl = ih.get_node_to_decl();
        std::cout << "the simplified covers:" << std::endl;
        for (int i = 0; i < covers.size(); i++) {
            func_decl decl = node_to_decl[i];
            std::string name = decl.name().str();
            if (ih.get_root_decl_id() == i) {
                name = "root";
            }
            else if (ih.get_error_decl_id() == i) {
                name = "error";
            }
            std::cout << "- " << name << ":\n\t";
            std::cout << covers[i].simplify() << "\n";
        }
    }
}

void z3_run(string fileName) {
    IH_MEASURE_FN;

    try {
        context c;
        fixedpoint fp(c);
        fp.set(init_params(c));
        expr error = c.bool_const("lazy_horn_error_relation");
        fp.from_file(fileName.c_str());
        expr_vector assertions = fp.assertions();
        int i = 0;
        for (expr_vector::iterator it = assertions.begin(); it != assertions.end(); ++it, ++i) {
            expr rule = *it;
            symbol name = c.str_symbol(("rule" + std::to_string(i)).c_str());

            expr head_rel = rule.body().arg(1);
            if (head_rel.is_false()) {
                func_decl error_decl = error.decl();
                fp.register_relation(error_decl);
                expr new_rule = implies(rule.body().arg(0), error);
                fp.add_rule(new_rule, name);
            }
            else {
                func_decl head_rel_decl = head_rel.decl();
                fp.register_relation(head_rel_decl);
                fp.add_rule(rule, name);
            }
        }

        check_result res = fp.query(error);
        if (res == z3::sat) {
            Stats::set("Result", "SAT");
        } else if (res == z3::unsat) {
            Stats::set("Result", "UNSAT");
        } else {
            Stats::set("Result", "UNKNOWN");
        }
    }
    catch (z3::exception& ex) {
        vout() << ex.msg() <<  "\n";
    }
    Z3_finalize_memory();
}

int main(int argc, char** argv) {
    std::string fileName = parseCmdLine(argc, argv);
    Stats::set("Result", "UNKNOWN");
    // VERBOSE(0, Stats::PrintBrunch(outs()););
    int ret = 0;
    if (gParams.alg == 0) {
        // Z3
        z3_run(fileName);
    } else if (gParams.alg == 1) {
        try{
            test_query(fileName);
        }
        catch (z3::exception& ex) {
            std::cout << "unexpected error: " << ex << "\n";
        }
    } else {
        assert(false);
    }

    VERBOSE(0, Stats::PrintBrunch(outs()););
    Z3_finalize_memory();
    return ret;
}
