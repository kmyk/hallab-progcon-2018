//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once

//------------------------------------------------------------------------------
#include "RandomSeed.hpp"

//------------------------------------------------------------------------------
namespace hpc {

/// 乱数生成器。
/// @attention 乱数生成処理を関数引数に直接書くと、
///            「関数引数の評価順序はコンパイラの実装に依存する」という特性上、
///            環境によって得られる乱数が異なるようになってしまいます。
///            環境への依存性をなくすには、
///            乱数を一度ローカル変数で受けてから関数に渡す、などの対策をとってください。
///
///            影響を受ける例:
///              someFunction(random.randU32(), random.randU32());
///
///            影響を受けなくした例:
///              auto v1 = random.randU32();
///              auto v2 = random.randU32();
///              someFunction(v1, v2);
class Random
{
public:
    /// @name コンストラクタ
    //@{
    /// 指定の乱数シードで初期化するコンストラクタ
    explicit Random(const RandomSeed& aRandomSeed);
    //@}

    /// @name 乱数生成
    //@{
    /// [0, aTerm) の範囲で乱数を生成する。
    int randTerm(int aTerm);
    /// [aMin, aTerm) の範囲で乱数を生成する。
    int randMinTerm(int aMin, int aTerm);
    /// [aMin, aMax] の範囲で乱数を生成する。
    int randMinMax(int aMin, int aMax);
    /// [0, 0xFFFFFFFF] の範囲で乱数を生成する。
    uint randU32();
    /// [aMin, aTerm) の範囲で乱数を生成する。
    float randFloatMinTerm(float aMin, float aTerm);
    /// [0, aTerm) の範囲で乱数を生成する。
    float randFloatTerm(float aTerm);
    /// [0, 1.0f) の範囲で乱数を生成する。
    float randFloat();
    /// あたらしく乱数シードを生成する
    RandomSeed generateRandomSeed();
    //@}

    /// @name 乱数管理
    //@{
    /// 乱数を空回しする
    void spin(int aCount);
    //@}

private:
    /// @name プライベートメンバ変数
    //@{
    /// 乱数シード。
    RandomSeed mRandomSeed;
    //@}
};

} // namespace
// EOF
