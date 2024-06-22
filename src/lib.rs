extern crate geo_types;
extern crate num_traits;

use std::fmt::Debug;
use std::io;
use std::io::prelude::*;

use geo_types::*;
use num_traits::Float;

/// Extension trait for `Read`
pub trait WKBReadExt {
    /// Attempt to read a Geometry<f64> from this reader
    fn read_wkb(&mut self) -> Result<Geometry<f64>, WKBReadError>;
}

impl<R: Read> WKBReadExt for R {
    #[inline]
    fn read_wkb(&mut self) -> Result<Geometry<f64>, WKBReadError> {
        wkb_to_geom(self)
    }
}

/// Extension trait for `Write`
pub trait WKBWriteExt {
    /// Attempt to write a Geometry<Into<f64>> to this writer.
    fn write_wkb<T>(&mut self, g: &Geometry<T>, is_little_endian: bool) -> Result<(), WKBWriteError>
    where
        T: Into<f64> + Float + Debug;
}

impl<W: Write> WKBWriteExt for W {
    fn write_wkb<T>(&mut self, g: &Geometry<T>, is_little_endian: bool) -> Result<(), WKBWriteError>
    where
        T: Into<f64> + Float + Debug,
    {
        write_geom_to_wkb(g, self, is_little_endian)
    }
}

/// An error occurred when reading
#[derive(Debug)]
pub enum WKBReadError {
    /// Within in the format, there was an unexpected or wrong data type
    WrongType,

    /// Underlying IO error from the Reader
    IOError(io::Error),
}

impl From<io::Error> for WKBReadError {
    fn from(err: io::Error) -> WKBReadError {
        WKBReadError::IOError(err)
    }
}

/// A thing (`Geometry`) that can be read or written as WKB
///
/// ```rust
/// # extern crate geo_types;
/// # extern crate wkb;
/// # fn main() {
/// use geo_types::*;
/// use wkb::*;
/// let p: Geometry<f64> = Geometry::Point(Point::new(2., 4.));
/// let mut bytes = Vec::new();
/// p.write_as_wkb(&mut bytes, true).unwrap();
/// assert_eq!(bytes, vec![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 16, 64]);
/// # }
/// ```
pub trait WKBAbleExt {
    /// Attempt to write self as WKB to a `Write`.
    fn write_as_wkb(&self, w: &mut impl Write, is_little_endian: bool) -> Result<(), WKBWriteError>;

    /// Return self as WKB bytes
    fn as_wkb_bytes(&self, is_little_endian: bool) -> Vec<u8> {
        let mut bytes = Vec::new();
        self.write_as_wkb(&mut bytes, is_little_endian).unwrap();
        bytes
    }

    /// Attempt to read an instance of self from this `Read`.
    fn read_from_wkb(r: &mut impl Read) -> Result<Self, WKBReadError>
    where
        Self: Sized;
}

impl WKBAbleExt for Geometry<f64> {
    fn write_as_wkb(&self, w: &mut impl Write, is_little_endian: bool) -> Result<(), WKBWriteError> {
        write_geom_to_wkb(self, w, is_little_endian)
    }

    fn read_from_wkb(r: &mut impl Read) -> Result<Self, WKBReadError> {
        wkb_to_geom(r)
    }
}

/// An error occurred when writing
#[derive(Debug)]
pub enum WKBWriteError {
    /// Geometry is a `geo_types::Rect`, which this library does not yet support
    UnsupportedGeoTypeRect,

    /// Geometry is a `geo_types::Triangle`, which this library does not yet support
    UnsupportedGeoTypeTriangle,

    /// An IO Error
    IOError(io::Error),
}

impl From<io::Error> for WKBWriteError {
    fn from(err: io::Error) -> WKBWriteError {
        WKBWriteError::IOError(err)
    }
}

fn read_f64<R: Read + ?Sized>(rdr: &mut R, is_little_endian: bool) -> Result<f64, std::io::Error> {
    let mut bytes = [0; 8];
    rdr.read_exact(&mut bytes)?;

    if is_little_endian {
        Ok(f64::from_le_bytes(bytes))
    } else {
        Ok(f64::from_be_bytes(bytes))
    }
}

fn read_u32<R: Read + ?Sized>(rdr: &mut R, is_little_endian: bool) -> Result<u32, std::io::Error> {
    let mut bytes = [0; 4];
    rdr.read_exact(&mut bytes)?;

    if is_little_endian {
        Ok(u32::from_le_bytes(bytes))
    } else {
        Ok(u32::from_be_bytes(bytes))
    }
}

fn read_u8<R: Read + ?Sized>(rdr: &mut R) -> Result<u8, std::io::Error> {
    let mut bytes = [0; 1];
    rdr.read_exact(&mut bytes)?;

    Ok(bytes[0])
}

fn read_point<R: Read + ?Sized>(rdr: &mut R, is_little_endian: bool) -> Result<Coord<f64>, WKBReadError> {
    let x = read_f64(rdr, is_little_endian)?;
    let y = read_f64(rdr, is_little_endian)?;
    Ok(Coord { x, y })
}

fn write_point<W: Write, T: Into<f64> + Float + Debug>(
    c: &Coord<T>,
    mut out: &mut W,
    is_little_endian: bool,
) -> Result<(), WKBWriteError> {
    if is_little_endian {
        out.write_all(&c.x.into().to_le_bytes())?;
        out.write_all(&c.y.into().to_le_bytes())?;
    } else {
        out.write_all(&c.x.into().to_be_bytes())?;
        out.write_all(&c.y.into().to_be_bytes())?;
    }
    Ok(())
}

fn read_many_points<R: Read + ?Sized>(rdr: &mut R, is_little_endian: bool) -> Result<Vec<Coord<f64>>, WKBReadError> {
    let num_points = read_u32(rdr, is_little_endian)? as usize;
    let mut res = Vec::with_capacity(num_points);
    for _ in 0..num_points {
        res.push(read_point(rdr, is_little_endian)?);
    }

    Ok(res)
}

fn write_many_points<W: Write, T: Into<f64> + Float + Debug>(
    mp: &[Coord<T>],
    mut out: &mut W,
    is_little_endian: bool,
) -> Result<(), WKBWriteError> {
    if is_little_endian {
        out.write_all(&(mp.len() as u32).to_le_bytes())?;
    } else {
        out.write_all(&(mp.len() as u32).to_be_bytes())?;
    }
    for p in mp.iter() {
        write_point(p, &mut out, is_little_endian)?;
    }

    Ok(())
}

/// Convert a Geometry into WKB bytes.
pub fn geom_to_wkb<T: Into<f64> + Float + Debug>(geom: &Geometry<T>, is_little_endian: bool) -> Result<Vec<u8>, WKBWriteError> {
    let mut result: Vec<u8> = Vec::new();
    write_geom_to_wkb(geom, &mut result, is_little_endian)?;
    Ok(result)
}

/// Write a geometry to the underlying writer, except for the endianness byte.
pub fn write_geom_to_wkb<W, T>(
    geom: &Geometry<T>,
    mut result: &mut W,
    is_little_endian: bool,
) -> Result<(), WKBWriteError>
where
    T: Into<f64> + Float + Debug,
    W: Write + ?Sized,
{
    if is_little_endian {
        result.write(&[1])?; // Little endian
    } else {
        result.write(&[0])?; // Big endian
    }

    match geom {
        Geometry::Point(p) => {
            result.write_all(&1_u32.to_le_bytes())?;
            write_point(&p.0, &mut result, is_little_endian)?;
        }
        Geometry::LineString(ls) => {
            result.write_all(&2_u32.to_le_bytes())?;
            write_many_points(&ls.0, &mut result, is_little_endian)?;
        }
        Geometry::Line(l) => {
            write_many_points(&[l.start, l.end], &mut result, is_little_endian)?;
        }
        Geometry::Polygon(p) => {
            result.write_all(&3_u32.to_le_bytes())?;
            result.write_all(&(1 + p.interiors().len() as u32).to_le_bytes())?;
            write_many_points(&p.exterior().0, &mut result, is_little_endian)?;
            for i in p.interiors().iter() {
                write_many_points(&i.0, &mut result, is_little_endian)?;
            }
        }
        Geometry::MultiPoint(mp) => {
            result.write_all(&4_u32.to_le_bytes())?;
            result.write_all(&(mp.0.len() as u32).to_le_bytes())?;
            for point in &mp.0 {
                if is_little_endian {
                    result.write(&[1])?;
                } else {
                    result.write(&[0])?;
                }
                result.write_all(&1_u32.to_le_bytes())?;
                write_point(&point.0, &mut result, is_little_endian)?;
            }
        }
        Geometry::MultiLineString(mls) => {
            result.write_all(&5_u32.to_le_bytes())?;
            result.write_all(&(mls.0.len() as u32).to_le_bytes())?;
            for ls in mls.0.iter() {
                if is_little_endian {
                    result.write(&[1])?; // Little endian
                } else {
                    result.write(&[0])?; // Big endian
                }
                result.write_all(&2_u32.to_le_bytes())?;
                write_many_points(&ls.0, &mut result, is_little_endian)?;
            }
        }
        Geometry::MultiPolygon(mp) => {
            result.write_all(&6_u32.to_le_bytes())?;
            result.write_all(&(mp.0.len() as u32).to_le_bytes())?;
            for poly in mp.0.iter() {
                if is_little_endian {
                    result.write(&[1])?; // Little endian
                } else {
                    result.write(&[0])?; // Big endian
                }
                result.write_all(&3_u32.to_le_bytes())?;
                result.write_all(&(1 + poly.interiors().len() as u32).to_le_bytes())?;
                write_many_points(&poly.exterior().0, &mut result, is_little_endian)?;
                for int in poly.interiors().iter() {
                    write_many_points(&int.0, &mut result, is_little_endian)?;
                }
            }
        }
        Geometry::GeometryCollection(gc) => {
            result.write_all(&7_u32.to_le_bytes())?;
            result.write_all(&(gc.len() as u32).to_le_bytes())?;
            for geom in gc.0.iter() {
                write_geom_to_wkb(geom, result, is_little_endian)?;
            }
        }
        Geometry::Rect(_rect) => {
            return Err(WKBWriteError::UnsupportedGeoTypeRect);
        }
        Geometry::Triangle(_t) => {
            return Err(WKBWriteError::UnsupportedGeoTypeTriangle);
        }
    }

    Ok(())
}



/// Read a Geometry from a reader. Converts WKB to a Geometry.
fn wkb_to_geom<R>(wkb: &mut R) -> Result<Geometry<f64>, WKBReadError>
where
    R: Read + ?Sized,
{
    let is_little_endian = match read_u8(wkb)? {
        0 => false, // BigEndian
        1 => true,  // LittleEndian
        _ => return Err(WKBReadError::WrongType),
    };

    let type_id = read_u32(wkb, is_little_endian)?;
    println!("Type ID: {}", type_id);

    match type_id {
        1 => {
            // Point
            let point = read_point(wkb, is_little_endian)?;
            Ok(Geometry::Point(Point(point)))
        }
        2 => {
            // LineString
            let points = read_many_points(wkb, is_little_endian)?;
            Ok(Geometry::LineString(LineString(points)))
        }
        3 => {
            // Polygon
            let num_rings = read_u32(wkb, is_little_endian)? as usize;
            println!("Number of Rings: {}", num_rings);
            let exterior = read_many_points(wkb, is_little_endian)?;
            let mut interiors = Vec::with_capacity(num_rings - 1);
            for _ in 0..(num_rings - 1) {
                interiors.push(LineString(read_many_points(wkb, is_little_endian)?));
            }
            Ok(Geometry::Polygon(Polygon::new(
                LineString(exterior),
                interiors,
            )))
        }
        4 => {
            // MultiPoint
            let num_points = read_u32(wkb, is_little_endian)? as usize;
            println!("Number of Points: {}", num_points);
            let mut points = Vec::with_capacity(num_points);
            for _ in 0..num_points {
                let _ = read_u8(wkb)?; // Read the endianness byte for each Point
                let point_type_id = read_u32(wkb, is_little_endian)?;
                if point_type_id != 1 {
                    println!("Point Type ID: {:?}", point_type_id);
                    return Err(WKBReadError::WrongType);
                }
                let point = read_point(wkb, is_little_endian)?;
                points.push(Point(point));
            }
            Ok(Geometry::MultiPoint(MultiPoint(points)))
        }
        5 => {
            // MultiLineString
            let num_linestrings = read_u32(wkb, is_little_endian)? as usize;
            println!("Number of LineStrings: {}", num_linestrings);
            let mut linestrings = Vec::with_capacity(num_linestrings);
            for _ in 0..num_linestrings {
                let linestring: LineString<f64> = match wkb_to_geom(wkb)? {
                    Geometry::LineString(l) => l,
                    _ => {
                        return Err(WKBReadError::WrongType);
                    }
                };

                linestrings.push(linestring);
            }
            Ok(Geometry::MultiLineString(MultiLineString(linestrings)))
        }
        6 => {
            // MultiPolygon
            let num_polygons = read_u32(wkb, is_little_endian)? as usize;
            println!("Number of Polygons: {}", num_polygons);
            let mut polygons = Vec::with_capacity(num_polygons);
            for _ in 0..num_polygons {
                let polygon_geom = wkb_to_geom(wkb)?;
                println!("MultiPolygon Type ID: {:?}", polygon_geom);
                if let Geometry::Polygon(p) = polygon_geom {
                    polygons.push(p);
                } else {
                    return Err(WKBReadError::WrongType);
                }
            }
            Ok(Geometry::MultiPolygon(MultiPolygon(polygons)))
        }
        7 => {
            // GeometryCollection
            let num_geometries = read_u32(wkb, is_little_endian)? as usize;
            println!("Number of Geometries: {}", num_geometries);
            let mut geometries = Vec::with_capacity(num_geometries);
            for _ in 0..num_geometries {
                geometries.push(wkb_to_geom(wkb)?);
            }
            Ok(Geometry::GeometryCollection(GeometryCollection(geometries)))
        }
        _ => Err(WKBReadError::WrongType),
    }
}





#[cfg(test)]
mod tests {
    use super::*;

    fn assert_two_f64(mut reader: &mut impl Read, a: impl Into<f64>, b: impl Into<f64>) {
        assert_eq!(read_f64(&mut reader, true).unwrap(), a.into());
        assert_eq!(read_f64(&mut reader, true).unwrap(), b.into());
    }

    fn write_two_f64<W: Write>(writer: &mut W, a: impl Into<f64>, b: impl Into<f64>) {
        writer.write_all(&a.into().to_le_bytes()).unwrap();
        writer.write_all(&b.into().to_le_bytes()).unwrap();
    }

    #[test]
    fn point_to_wkb() {
        let p: Geometry<f64> = Geometry::Point(Point::new(2., 4.));
        let res = geom_to_wkb(&p, true).unwrap();
        let mut res = res.as_slice();
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 1);
        assert_two_f64(&mut res, 2, 4);

        assert_eq!(
            wkb_to_geom(&mut geom_to_wkb(&p, true).unwrap().as_slice()).unwrap(),
            p
        );
    }

    #[test]
    fn wkb_to_point() {
        let mut bytes = Vec::new();
        bytes.write(&[1]).unwrap();
        bytes.write_all(&(1_u32).to_le_bytes()).unwrap();
        bytes.write_all(&(100f64).to_le_bytes()).unwrap();
        bytes.write_all(&(-2f64).to_le_bytes()).unwrap();

        let geom = wkb_to_geom(&mut bytes.as_slice()).unwrap();
        if let Geometry::Point(p) = geom {
            assert_eq!(p.x(), 100.);
            assert_eq!(p.y(), -2.);
        } else {
            assert!(false);
        }

        assert_eq!(
            geom_to_wkb(&wkb_to_geom(&mut bytes.as_slice()).unwrap(), true).unwrap(),
            bytes
        );
    }

    #[test]
    fn linestring_to_wkb() {
        let ls: LineString<f64> = vec![(0., 0.), (1., 0.), (1., 1.), (0., 1.), (0., 0.)].into();
        let ls = Geometry::LineString(ls);

        let res = geom_to_wkb(&ls, true).unwrap();
        let mut res = res.as_slice();
        assert_eq!(read_u8(&mut res).unwrap(), 1); // LittleEndian
        assert_eq!(read_u32(&mut res, true).unwrap(), 2); // 2 = Linestring
        assert_eq!(read_u32(&mut res, true).unwrap(), 5); // num points

        assert_two_f64(&mut res, 0, 0);
        assert_two_f64(&mut res, 1, 0);
        assert_two_f64(&mut res, 1, 1);
        assert_two_f64(&mut res, 0, 1);
        assert_two_f64(&mut res, 0, 0);

        assert_eq!(
            wkb_to_geom(&mut geom_to_wkb(&ls, true).unwrap().as_slice()).unwrap(),
            ls
        );
    }

    #[test]
    fn wkb_to_linestring() {
        let mut bytes = Vec::new();
        bytes.write(&[1]).unwrap();

        bytes.write_all(&(2_u32).to_le_bytes()).unwrap();
        bytes.write_all(&(2_u32).to_le_bytes()).unwrap();

        write_two_f64(&mut bytes, 0, 0);
        write_two_f64(&mut bytes, 1000, 1000);

        let geom = wkb_to_geom(&mut bytes.as_slice()).unwrap();
        if let Geometry::LineString(ls) = geom {
            assert_eq!(ls.0.len(), 2);
            assert_eq!(ls.0[0].x, 0.);
            assert_eq!(ls.0[0].y, 0.);
            assert_eq!(ls.0[1].x, 1000.);
            assert_eq!(ls.0[1].y, 1000.);
        } else {
            assert!(false);
        }

        assert_eq!(
            geom_to_wkb(&wkb_to_geom(&mut bytes.as_slice()).unwrap(), true).unwrap(),
            bytes
        );
    }

    #[test]
    fn polygon_to_wkb() {
        let ls = vec![(0., 0.), (10., 0.), (10., 10.), (0., 10.), (0., 0.)].into();
        let int = vec![(2., 2.), (2., 4.), (4., 4.), (4., 2.), (2., 2.)].into();
        let p = Geometry::Polygon(Polygon::new(ls, vec![int]));

        let res = geom_to_wkb(&p, true).unwrap();
        let mut res = res.as_slice();
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 3);
        assert_eq!(read_u32(&mut res, true).unwrap(), 2);

        // Exterior Ring
        assert_eq!(read_u32(&mut res, true).unwrap(), 5);

        assert_two_f64(&mut res, 0, 0);
        assert_two_f64(&mut res, 10, 0);
        assert_two_f64(&mut res, 10, 10);
        assert_two_f64(&mut res, 0, 10);
        assert_two_f64(&mut res, 0, 0);

        // interior ring
        assert_eq!(read_u32(&mut res, true).unwrap(), 5);

        assert_two_f64(&mut res, 2, 2);
        assert_two_f64(&mut res, 2, 4);
        assert_two_f64(&mut res, 4, 4);
        assert_two_f64(&mut res, 4, 2);
        assert_two_f64(&mut res, 2, 2);

        assert_eq!(
            wkb_to_geom(&mut geom_to_wkb(&p, true).unwrap().as_slice()).unwrap(),
            p
        );
    }

    #[test]
    fn wkb_to_polygon() {
        let mut bytes = Vec::new();
        bytes.write(&[1]).unwrap();
        bytes.write_all(&(3_u32).to_le_bytes()).unwrap();
        bytes.write_all(&(1_u32).to_le_bytes()).unwrap();
        bytes.write_all(&(4_u32).to_le_bytes()).unwrap();

        write_two_f64(&mut bytes, 0, 0);
        write_two_f64(&mut bytes, 1, 0);
        write_two_f64(&mut bytes, 0, 1);
        // WKB requires that polygons are closed
        write_two_f64(&mut bytes, 0, 0);

        let geom = wkb_to_geom(&mut bytes.as_slice()).unwrap();
        if let Geometry::Polygon(p) = geom {
            assert_eq!(p.interiors().len(), 0);
            assert_eq!(p.exterior().0.len(), 4);
            assert_eq!(p.exterior().0[0], (0., 0.).into());
            assert_eq!(p.exterior().0[1], (1., 0.).into());
            assert_eq!(p.exterior().0[2], (0., 1.).into());
            assert_eq!(p.exterior().0[3], (0., 0.).into());
        } else {
            assert!(false);
        }

        assert_eq!(
            geom_to_wkb(&wkb_to_geom(&mut bytes.as_slice()).unwrap(), true).unwrap(),
            bytes
        );
    }

    #[test]
    fn wkb_to_polygon_auto_closed() {
        let mut bytes = Vec::new();
        bytes.write(&[1]).unwrap();
        bytes.write_all(&(3_u32).to_le_bytes()).unwrap();
        bytes.write_all(&(1_u32).to_le_bytes()).unwrap();

        // only 3 points
        bytes.write_all(&(3_u32).to_le_bytes()).unwrap();

        write_two_f64(&mut bytes, 0, 0);
        write_two_f64(&mut bytes, 1, 0);
        write_two_f64(&mut bytes, 0, 1);

        let geom = wkb_to_geom(&mut bytes.as_slice()).unwrap();
        if let Geometry::Polygon(p) = geom {
            assert_eq!(p.interiors().len(), 0);
            assert_eq!(p.exterior().0[0], (0., 0.).into());
            assert_eq!(p.exterior().0[1], (1., 0.).into());
            assert_eq!(p.exterior().0[2], (0., 1.).into());

            // And yet, the geo-types library has add this point
            assert_eq!(p.exterior().0[3], (0., 0.).into());
            assert_eq!(p.exterior().0.len(), 4);
        } else {
            assert!(false);
        }

        // They won't equal
        assert_ne!(
            geom_to_wkb(&wkb_to_geom(&mut bytes.as_slice()).unwrap(), true).unwrap(),
            bytes
        );
    }

    #[test]
    fn multipoint_to_wkb() {
        let p: Geometry<f64> =
            Geometry::MultiPoint(MultiPoint(vec![Point::new(0., 0.), Point::new(10., -2.)]));
        let res = geom_to_wkb(&p, true).unwrap();
        let mut res = res.as_slice();
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 4);
        assert_eq!(read_u32(&mut res, true).unwrap(), 2);

        // Point 1
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 1);
        assert_two_f64(&mut res, 0, 0);

        // Point 2
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 1);
        assert_two_f64(&mut res, 10, -2);

        assert_eq!(
            wkb_to_geom(&mut geom_to_wkb(&p, true).unwrap().as_slice()).unwrap(),
            p
        );
    }

    #[test]
    fn wkb_to_multipoint() {
        let mut bytes = Vec::new();
        bytes.write(&[1]).unwrap();
        bytes.write_all(&(4_u32).to_le_bytes()).unwrap();
        bytes.write_all(&(1_u32).to_le_bytes()).unwrap();
        write_two_f64(&mut bytes, 100, -2);

        let geom = wkb_to_geom(&mut bytes.as_slice()).unwrap();
        if let Geometry::MultiPoint(mp) = geom {
            assert_eq!(mp.0.len(), 1);
            assert_eq!(mp.0[0].x(), 100.);
            assert_eq!(mp.0[0].y(), -2.);
        } else {
            assert!(false);
        }

        assert_eq!(
            geom_to_wkb(&wkb_to_geom(&mut bytes.as_slice()).unwrap(), true).unwrap(),
            bytes
        );
    }

    #[test]
    fn multilinestring_to_wkb() {
        let ls = Geometry::MultiLineString(MultiLineString(vec![
            vec![(0., 0.), (1., 1.)].into(),
            vec![(10., 10.), (10., 11.)].into(),
        ]));

        let res = geom_to_wkb(&ls, true).unwrap();
        let mut res = res.as_slice();
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 5); // 5 - MultiLineString
        assert_eq!(read_u32(&mut res, true).unwrap(), 2); // 2 linestrings

        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 2); // 2 = Linestring
        assert_eq!(read_u32(&mut res, true).unwrap(), 2); // num points
        assert_two_f64(&mut res, 0, 0);
        assert_two_f64(&mut res, 1, 1);

        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 2); // 2 = Linestring
        assert_eq!(read_u32(&mut res, true).unwrap(), 2); // num points
        assert_two_f64(&mut res, 10, 10);
        assert_two_f64(&mut res, 10, 11);

        assert_eq!(
            wkb_to_geom(&mut geom_to_wkb(&ls, true).unwrap().as_slice()).unwrap(),
            ls
        );
    }

    #[test]
    fn wkb_to_multilinestring() {
        let mut bytes = Vec::new();
        bytes.write(&[1]).unwrap();
        bytes.write_all(&(5_u32).to_le_bytes()).unwrap();
        bytes.write_all(&(2_u32).to_le_bytes()).unwrap();

        bytes.write(&[1]).unwrap();
        bytes.write_all(&(2_u32).to_le_bytes()).unwrap();
        bytes.write_all(&(2_u32).to_le_bytes()).unwrap();
        write_two_f64(&mut bytes, 0, 0);
        write_two_f64(&mut bytes, 1, 0);

        bytes.write(&[1]).unwrap();
        bytes.write_all(&(2_u32).to_le_bytes()).unwrap();
        bytes.write_all(&(2_u32).to_le_bytes()).unwrap();
        write_two_f64(&mut bytes, 10, 10);
        write_two_f64(&mut bytes, 20, 20);

        let geom = wkb_to_geom(&mut bytes.as_slice()).unwrap();
        if let Geometry::MultiLineString(mls) = geom {
            assert_eq!(mls.0.len(), 2);
            assert_eq!(mls.0[0].0.len(), 2);
            assert_eq!(mls.0[0].0[0].x_y(), (0., 0.));
            assert_eq!(mls.0[0].0[1].x_y(), (1., 0.));
            assert_eq!(mls.0[1].0.len(), 2);
            assert_eq!(mls.0[1].0[0].x_y(), (10., 10.));
            assert_eq!(mls.0[1].0[1].x_y(), (20., 20.));
        } else {
            assert!(false);
        }

        assert_eq!(
            geom_to_wkb(&wkb_to_geom(&mut bytes.as_slice()).unwrap(), true).unwrap(),
            bytes
        );
    }

    #[test]
    fn multipolygon_to_wkb() {
        let ls = vec![(0., 0.), (10., 0.), (10., 10.), (0., 10.), (0., 0.)].into();
        let int = vec![(2., 2.), (2., 4.), (2., 2.)].into();

        let p1 = Polygon::new(ls, vec![]);
        let p2 = Polygon::new(int, vec![]);
        let p = Geometry::MultiPolygon(MultiPolygon(vec![p1, p2]));

        let res = geom_to_wkb(&p, true).unwrap();
        let mut res = res.as_slice();
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 6); // Multipolygon
        assert_eq!(read_u32(&mut res, true).unwrap(), 2); // num polygons

        // polygon 1
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 3); // polygon
        assert_eq!(read_u32(&mut res, true).unwrap(), 1); // only one ring

        assert_eq!(read_u32(&mut res, true).unwrap(), 5); // 5 points in ring #1
        assert_two_f64(&mut res, 0, 0);
        assert_two_f64(&mut res, 10, 0);
        assert_two_f64(&mut res, 10, 10);
        assert_two_f64(&mut res, 0, 10);
        assert_two_f64(&mut res, 0, 0);

        // polygon 2
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 3); // polygon
        assert_eq!(read_u32(&mut res, true).unwrap(), 1); // one ring
        assert_eq!(read_u32(&mut res, true).unwrap(), 3); // 3 points in ring #1

        assert_two_f64(&mut res, 2, 2);
        assert_two_f64(&mut res, 2, 4);
        assert_two_f64(&mut res, 2, 2);

        assert_eq!(
            wkb_to_geom(&mut geom_to_wkb(&p, true).unwrap().as_slice()).unwrap(),
            p
        );
    }

    #[test]
    fn postgis_wkb_to_multipolygon() {
        let bytes: Vec<u8> = vec![
            0x01, 0x06, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x01, 0x03, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x24, 0x40,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x24, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x01, 0x03, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x04,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
            0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40,
        ];

        let geom = wkb_to_geom(&mut bytes.as_slice()).unwrap();

        if let Geometry::MultiPolygon(mp) = geom {
            assert_eq!(mp.0.len(), 2);
            assert_eq!(mp.0[0].exterior().0.len(), 5);
            assert_eq!(mp.0[0].exterior().0[0].x_y(), (0., 0.));
            assert_eq!(mp.0[0].exterior().0[1].x_y(), (10., 0.));
            assert_eq!(mp.0[0].exterior().0[2].x_y(), (10., 10.));
            assert_eq!(mp.0[0].exterior().0[3].x_y(), (0., 10.));
            assert_eq!(mp.0[0].exterior().0[4].x_y(), (0., 0.));

            assert_eq!(mp.0[0].interiors().len(), 0);

            assert_eq!(mp.0[1].exterior().0.len(), 4);
            assert_eq!(mp.0[1].exterior().0[0].x_y(), (2., 2.));
            assert_eq!(mp.0[1].exterior().0[1].x_y(), (2., 4.));
            assert_eq!(mp.0[1].exterior().0[2].x_y(), (4., 2.));
            assert_eq!(mp.0[1].exterior().0[0].x_y(), (2., 2.));
            assert_eq!(mp.0[1].interiors().len(), 0);
        } else {
            assert!(false);
        }
    }

    #[test]
    fn geometrycollection_to_wkb() {
        let p: Geometry<_> = Point::new(0., 0.).into();
        let l: Geometry<_> = LineString(vec![(10., 0.).into(), (20., 0.).into()]).into();
        let gc: Geometry<_> = Geometry::GeometryCollection(GeometryCollection(vec![p, l]));

        let res = geom_to_wkb(&gc, true).unwrap();
        let mut res = res.as_slice();
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 7); // geometry collection
        assert_eq!(read_u32(&mut res, true).unwrap(), 2);
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 1); // point
        assert_two_f64(&mut res, 0, 0);
        assert_eq!(read_u8(&mut res).unwrap(), 1);
        assert_eq!(read_u32(&mut res, true).unwrap(), 2);
        assert_eq!(read_u32(&mut res, true).unwrap(), 2);
        assert_two_f64(&mut res, 10, 0);
        assert_two_f64(&mut res, 20, 0);
    }

    #[test]
    fn test_simple_multilinestring1() {
        let mut wkb: Vec<u8> = vec![
            1, 5, 0, 0, 0, 1, 0, 0, 0,   // MultiLineString type ID and number of LineStrings
            1, 2, 0, 0, 0,               // LineString type ID and number of points
            0, 0, 0, 0, 0, 0, 0, 0,      // Point 1 coordinates
            0, 0, 0, 0, 0, 0, 0, 0,      
            0, 0, 0, 0, 0, 0, 0, 0,      // Point 2 coordinates (0.0, 0.0)
            0, 0, 0, 0, 0, 0, 240, 63,   // Point 3 coordinates (1.0, 1.0)
        ];
    
        let geom = wkb_to_geom(&mut wkb.as_slice()).unwrap();
        assert_eq!(
            geom,
            Geometry::MultiLineString(MultiLineString(vec![vec![(0., 0.), (1., 1.)].into()]))
        );
    }
    
    

    #[test]
    fn test_simple_multilinestring2() {
        let wkb: Vec<u8> = vec![1, 5, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 240, 0, 0, 0, 0, 0, 0, 63, 240, 1, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 132, 0, 0, 0, 0, 0, 0, 64]
        ;
        

        let geom = wkb_to_geom(&mut wkb.as_slice()).unwrap();
        assert_eq!(
            geom,
            Geometry::MultiLineString(MultiLineString(vec![
                vec![(0., 0.), (1., 1.)].into(),
                vec![(2., 2.), (3., 2.)].into(),
            ]))
        );
    }

    #[test]
    fn bigendian_supported() {
        let mut bytes = Vec::new();
        bytes.write(&[0]).unwrap();
        bytes.write_all(&1_u32.to_be_bytes()).unwrap();
        bytes.write_all(&(100f64).to_be_bytes()).unwrap();
        bytes.write_all(&(-2f64).to_be_bytes()).unwrap();

        let geom = wkb_to_geom(&mut bytes.as_slice()).unwrap();
        if let Geometry::Point(p) = geom {
            assert_eq!(p.x(), 100.);
            assert_eq!(p.y(), -2.);
        } else {
            assert!(false);
        }
    }

    #[test]
    fn wkb_to_geometrycollection() {
        let original_collection = GeometryCollection(vec![
            Geometry::Point(Point::new(1.5, 2.5)),
            Geometry::LineString(line_string![(x: 0.5, y: 0.5), (x: 5.5, y: 5.5)]),
        ]);
        let original_geometry = Geometry::GeometryCollection(original_collection);
        let wkb = geom_to_wkb(&original_geometry, true).unwrap();
        let parsed_geometry = wkb_to_geom(&mut wkb.as_slice()).unwrap();
        assert_eq!(original_geometry, parsed_geometry);
    }
}
