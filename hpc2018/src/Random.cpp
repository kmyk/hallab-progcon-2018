//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "Random.hpp"

//------------------------------------------------------------------------------
#include "Assert.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
Random::Random(const RandomSeed& aRandomSeed)
: mRandomSeed(aRandomSeed)
{
}

//------------------------------------------------------------------------------
int Random::randTerm(int aTerm)
{
    HPC_ASSERT_GREATER_I(aTerm, 0);
    return int(randU32() & 0x7FFFFFFF) % aTerm;
}

//------------------------------------------------------------------------------
int Random::randMinTerm(int aMin, int aTerm)
{
    HPC_ASSERT_LESS_EQUAL_I(aMin, aTerm - 1);
    return aMin + randTerm(aTerm - aMin);
}

//------------------------------------------------------------------------------
int Random::randMinMax(int aMin, int aMax)
{
    HPC_ASSERT_LESS_EQUAL_I(aMin, aMax);
    return aMin + randTerm(1 + aMax - aMin);
}

//------------------------------------------------------------------------------
uint Random::randU32()
{
    const uint t = (mRandomSeed.x ^ (mRandomSeed.x << 11));
    mRandomSeed.x = mRandomSeed.y;
    mRandomSeed.y = mRandomSeed.z;
    mRandomSeed.z = mRandomSeed.w;
    mRandomSeed.w =
        (mRandomSeed.w ^ (mRandomSeed.w >> 19)) ^ (t ^ (t >> 8));

    return mRandomSeed.w;
}

//------------------------------------------------------------------------------
float Random::randFloatMinTerm(float aMin, float aTerm)
{
    HPC_ASSERT_GREATER_F(aTerm, aMin);
    return aMin + randFloat() * (aTerm - aMin);
}

//------------------------------------------------------------------------------
float Random::randFloatTerm(float aTerm)
{
    return randFloatMinTerm(0.0f, aTerm);
}

//------------------------------------------------------------------------------
float Random::randFloat()
{
    return static_cast<float>(randU32() % 0x10000) / static_cast<float>(0x10000);
}

//------------------------------------------------------------------------------
RandomSeed Random::generateRandomSeed()
{
    // 乱数は、かならず一度ローカル変数で値を受けてから使うこと。
    // 引数に直接乱数呼び出しを書くと、
    // 環境によって引数の評価順序が異なり、
    // 異なる乱数が生成されることになる。
    const uint w = randU32();
    const uint z = randU32();
    const uint y = randU32();
    const uint x = randU32();
    return RandomSeed(x, y, z, w);
}

//------------------------------------------------------------------------------
void Random::spin(int aCount)
{
    for (int i = 0; i < aCount; ++i) {
        (void)randU32();
    }
}

} // namespace
// EOF
