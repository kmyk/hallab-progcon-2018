//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "Vector2i.hpp"

//------------------------------------------------------------------------------
#include "Math.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
Vector2i Vector2i::Zero()
{
    return Vector2i();
}

//------------------------------------------------------------------------------
Vector2i::Vector2i()
: x()
, y()
{
}

//------------------------------------------------------------------------------
Vector2i::Vector2i(int aX, int aY)
: x(aX)
, y(aY)
{
}

//------------------------------------------------------------------------------
bool Vector2i::operator==(const Vector2i& aRhs) const
{
    return x == aRhs.x && y == aRhs.y;
}

//------------------------------------------------------------------------------
bool Vector2i::isZeroStrict() const
{
    return x == 0 && y == 0;
}

//------------------------------------------------------------------------------
bool Vector2i::equals(const Vector2i& aVec) const
{
    return x == aVec.x && y == aVec.y;
}

//------------------------------------------------------------------------------
Vector2i Vector2i::operator-() const
{
    return Vector2i(-x, -y);
}

//------------------------------------------------------------------------------
Vector2i& Vector2i::operator+=(const Vector2i& aRhs)
{
    x += aRhs.x;
    y += aRhs.y;

    return *this;
}

//------------------------------------------------------------------------------
Vector2i& Vector2i::operator-=(const Vector2i& aRhs)
{
    x -= aRhs.x;
    y -= aRhs.y;

    return *this;
}

//------------------------------------------------------------------------------
Vector2i& Vector2i::operator*=(int aRhs)
{
    x *= aRhs;
    y *= aRhs;

    return *this;
}

//------------------------------------------------------------------------------
Vector2i Vector2i::operator+(const Vector2i& aRhs) const
{
    Vector2i v(*this);
    v += aRhs;

    return v;
}

//------------------------------------------------------------------------------
Vector2i Vector2i::operator-(const Vector2i& aRhs) const
{
    Vector2i v(*this);
    v -= aRhs;

    return v;
}

//------------------------------------------------------------------------------
Vector2i Vector2i::operator*(int aRhs) const
{
    Vector2i v(*this);
    v *= aRhs;

    return v;
}

//------------------------------------------------------------------------------
Vector2i operator*(int aLhs, const Vector2i& aRhs)
{
    return aRhs * aLhs;
}

//------------------------------------------------------------------------------
Vector2i Vector2i::min(const Vector2i& aVal) const
{
    return Vector2i(
        Math::Min(x, aVal.x),
        Math::Min(y, aVal.y)
        );
}

//------------------------------------------------------------------------------
Vector2i Vector2i::max(const Vector2i& aVal) const
{
    return Vector2i(
        Math::Max(x, aVal.x),
        Math::Max(y, aVal.y)
        );
}

//------------------------------------------------------------------------------
float Vector2i::length() const
{
    return Math::Sqrt(squareLength());
}

//------------------------------------------------------------------------------
float Vector2i::squareLength() const
{
    return static_cast<float>(x * x + y * y);
}

//------------------------------------------------------------------------------
float Vector2i::dist(const Vector2i& aPoint) const
{
    return Math::Sqrt(squareDist(aPoint));
}

//------------------------------------------------------------------------------
float Vector2i::squareDist(const Vector2i& aPoint) const
{
    const float x2 = static_cast<float>((aPoint.x - x) * (aPoint.x - x));
    const float y2 = static_cast<float>((aPoint.y - y) * (aPoint.y - y));

    return x2 + y2;
}

} // namespace
// EOF
