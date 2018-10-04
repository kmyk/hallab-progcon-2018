//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
// メインとなる cpp に #pragma once を書くと
// コンパイラによっては警告が出るため、
// ここには #pragma once は書きません。

#include "Print.hpp"
#include "Simulator.hpp"

#include <cstring>
#include <cstdlib>

//------------------------------------------------------------------------------
namespace {
    hpc::Simulator fSim;
}

//------------------------------------------------------------------------------
int main(int aArgc, const char* aArgv[])
{
    bool willPrintJson = false;
    bool silentMode = false;
    if (aArgc > 1) {
        for (int n = 1; n < aArgc; ++n) {
            // 引数がある場合、引数を記憶します。
            if (std::strcmp(aArgv[n], "-j") == 0) {
                willPrintJson = true;
            } else if (std::strcmp(aArgv[n], "-r") == 0) {
                if (n + 4 < aArgc) {
                    hpc::RandomSeed seed = hpc::RandomSeed::DefaultSeed();
                    seed.x = uint(std::strtoul(aArgv[n + 1], nullptr, 0));
                    seed.y = uint(std::strtoul(aArgv[n + 2], nullptr, 0));
                    seed.z = uint(std::strtoul(aArgv[n + 3], nullptr, 0));
                    seed.w = uint(std::strtoul(aArgv[n + 4], nullptr, 0));

                    if (seed.x == 0 && seed.y == 0 && seed.z == 0 && seed.w == 0) {
                        HPC_PRINTF("Invalid Argument.(-r) requires at least one non-zero seed value.\n");
                        return 1;
                    }

                    fSim.changeSeed(seed);
                    n += 4;
                } else {
                    HPC_PRINTF("Invalid Argument.(-r) requires four seed values.\n");
                    return 1;
                }
            } else if (!std::strcmp(aArgv[n], "-s")) {
                silentMode = true;
            } else {
                // 不明な引数
                HPC_PRINTF("Invalid Argument.(%s)\n", aArgv[n]);
                return 1;
            }
        }
    }

    fSim.run();

    if (willPrintJson) {
        // Jsonを出力します。
        fSim.printJson();
    } else {
        // 通常の出力を行います。
        fSim.printResult(silentMode);
    }

    return 0;
}

// EOF
