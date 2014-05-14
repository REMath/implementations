/*
 * PE_Header.java - This file is part of the Jakstab project.
 * 
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 * Copyright (C) 2003 The University of Arizona
 *
 * The original code for this class was taken from "MBEL: The Microsoft 
 * Bytecode Engineering Library" and modified for use with Jakstab.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, see <http://www.gnu.org/licenses/>.
 */

package org.jakstab.loader.pe;

import org.jakstab.loader.BinaryParseException;
import org.jakstab.util.BinaryInputBuffer;
import org.jakstab.util.Logger;

/** 
 * This class parses the PE header of a PE/COFF file
 * 
 * @author Michael Stepp
 * @author Johannes Kinder
 */
@SuppressWarnings("unused")
class PE_Header{
	private final static Logger logger = Logger.getLogger(PE_Header.class);

	public static final byte[] PE_TAG = new byte[]{80, 69, 0, 0}; // "PE\0\0"

	private static final int PE_SUBSYSTEM_NATIVE           = 1;
	private static final int PE_SUBSYSTEM_WINDOWS_GUI      = 2;
	private static final int PE_SUBSYSTEM_WINDOWS_CUI      = 3;
	private static final int PE_SUBSYSTEM_OS2_CUI          = 5;
	private static final int PE_SUBSYSTEM_POSIX_CUI        = 7;
	private static final int PE_SUBSYSTEM_NATIVE_WINDOWS   = 8;
	private static final int PE_SUBSYSTEM_WINDOWS_CE_GUI   = 9;
	// constants for the 'Subsystem' field
	private static final int PE32_MAGIC                    = 0x10b;
	private static final int PE32_PLUS_MAGIC               = 0x20b;

	private int Magic;                      // 2bytes
	private int MajorLinkerVersion;         // 1byte
	private int MinorLinkerVersion;         // 1byte
	private long SizeOfCode;                // 4bytes
	private long SizeOfInitializedData;     // 4bytes
	private long SizeOfUninitializedData;   // 4bytes
	private long AddressOfEntryPoint;       // 4byte RVA
	private long BaseOfCode;                // 4byte RVA
	// end of same format for PE32/PE32+
	private long BaseOfData;                // 4byte RVA
	// absent in PE32+


	// NT additional fields
	private long ImageBase;                    // 4byte VA
	private long SectionAlignment;             // 4bytes
	private long FileAlignment;                // 4bytes
	private int MajorOperatingSystemVersion;   // 2bytes
	private int MinorOperatingSystemVersion;   // 2bytes
	private int MajorImageVersion;             // 2bytes
	private int MinorImageVersion;             // 2bytes
	private int MajorSubsystemVersion;         // 2bytes
	private int MinorSubsystemVersion;         // 2bytes
	private long Win32VersionValue;            // 4bytes
	private long SizeOfImage;                  // 4bytes
	private long SizeOfHeaders;                // 4bytes
	private long CheckSum;                     // 4bytes
	private int Subsystem;                     // 2bytes
	private int DllCharacteristics;            // 2bytes
	private long SizeOfStackReserve;           // 4bytes
	private long SizeOfStackCommit;            // 4bytes
	private long SizeOfHeapReserve;            // 4bytes
	private long SizeOfHeapCommit;             // 4bytes
	private long LoaderFlags;                  // 4bytes
	private long NumberOfRvaAndSizes;          // 4bytes
	private ImageDataDirectory[] DataDirectory;// usually [16]


	/** 
	 * Parses a PE_Header from an input stream
	 */
	public PE_Header(BinaryInputBuffer in) throws java.io.IOException, BinaryParseException{
		Magic                   = in.readWORD();
		MajorLinkerVersion      = in.readBYTE();
		MinorLinkerVersion      = in.readBYTE();
		SizeOfCode              = in.readDWORD();
		SizeOfInitializedData   = in.readDWORD();
		SizeOfUninitializedData = in.readDWORD();
		AddressOfEntryPoint     = in.readDWORD();
		BaseOfCode              = in.readDWORD();

		if (Magic == PE32_MAGIC){
			// PE32 (normal)
			BaseOfData                    = in.readDWORD();
			ImageBase                     = in.readDWORD();
			SectionAlignment              = in.readDWORD();
			FileAlignment                 = in.readDWORD();
			MajorOperatingSystemVersion   = in.readWORD();
			MinorOperatingSystemVersion   = in.readWORD();
			MajorImageVersion             = in.readWORD();
			MinorImageVersion             = in.readWORD();
			MajorSubsystemVersion         = in.readWORD();
			MinorSubsystemVersion         = in.readWORD();
			Win32VersionValue             = in.readDWORD();
			SizeOfImage                   = in.readDWORD();
			SizeOfHeaders                 = in.readDWORD();
			CheckSum                      = in.readDWORD();
			Subsystem                     = in.readWORD();
			DllCharacteristics            = in.readWORD();
			// obsolete, ==0

			SizeOfStackReserve            = in.readDWORD();
			SizeOfStackCommit             = in.readDWORD();
			SizeOfHeapReserve             = in.readDWORD();
			SizeOfHeapCommit              = in.readDWORD();
			LoaderFlags                   = in.readDWORD();
			// obsolete, ==0

			NumberOfRvaAndSizes           = in.readDWORD();
		} else if (Magic == PE32_PLUS_MAGIC){
			// PE32+
			ImageBase                     = in.readDDWORD();
			SectionAlignment              = in.readDWORD();
			FileAlignment                 = in.readDWORD();
			MajorOperatingSystemVersion   = in.readWORD();
			MinorOperatingSystemVersion   = in.readWORD();
			MajorImageVersion             = in.readWORD();
			MinorImageVersion             = in.readWORD();
			MajorSubsystemVersion         = in.readWORD();
			MinorSubsystemVersion         = in.readWORD();
			Win32VersionValue             = in.readDWORD();
			SizeOfImage                   = in.readDWORD();
			SizeOfHeaders                 = in.readDWORD();
			CheckSum                      = in.readDWORD();
			Subsystem                     = in.readWORD();
			DllCharacteristics            = in.readWORD();
			// obsolete, ==0

			SizeOfStackReserve            = in.readDDWORD();
			SizeOfStackCommit             = in.readDDWORD();
			SizeOfHeapReserve             = in.readDDWORD();
			SizeOfHeapCommit              = in.readDDWORD();
			LoaderFlags                   = in.readDWORD();
			// obsolete, ==0

			NumberOfRvaAndSizes           = in.readDWORD();
		} else
			throw new BinaryParseException("PE_Header: Invalid magic number");

		DataDirectory = new ImageDataDirectory[(int)NumberOfRvaAndSizes];
		for (int i=0;i<NumberOfRvaAndSizes;i++)
			DataDirectory[i] = new ImageDataDirectory(in);
	}

	public void output(){
		logger.debug("PE Header:{");
		logger.debug("  Magic = " + "0x" + Integer.toHexString(Magic));
		logger.debug("  MajorLinkerVersion = " + MajorLinkerVersion);
		logger.debug("  MinorLinkerVersion = " + MinorLinkerVersion);
		logger.debug("  SizeOfCode = " + SizeOfCode);
		logger.debug("  SizeOfInitializedData = " + SizeOfInitializedData);
		logger.debug("  SizeOfUninitializedData = " + SizeOfUninitializedData);
		logger.debug("  AddressOfEntryPoint = " + "0x" + Long.toHexString(AddressOfEntryPoint));
		logger.debug("  BaseOfCode = " + "0x" + Long.toHexString(BaseOfCode));
		logger.debug("  BaseOfData = " + "0x" + Long.toHexString(BaseOfData));
		logger.debug("  /// NT Additional fields ////////");
		logger.debug("  ImageBase = " + "0x" + Long.toHexString(ImageBase));
		logger.debug("  SectionAlignment = " + "0x" + Long.toHexString(SectionAlignment));
		logger.debug("  FileAlignment = " + "0x" + Long.toHexString(FileAlignment));
		logger.debug("  MajorOperatingSystemVersion = " + MajorOperatingSystemVersion);
		logger.debug("  MinorOperatingSystemVersion = " + MinorOperatingSystemVersion);
		logger.debug("  MajorImageVersion = " + MajorImageVersion);
		logger.debug("  MinorImageVersion = " + MinorImageVersion);
		logger.debug("  MajorSubsystemVersion = " + MajorSubsystemVersion);
		logger.debug("  MinorSubsystemVersion = " + MinorSubsystemVersion);
		logger.debug("  Win32VersionValue = " + Win32VersionValue);
		logger.debug("  SizeOfImage = " + SizeOfImage);
		logger.debug("  SizeOfHeaders = " + SizeOfHeaders);
		logger.debug("  CheckSum = " + "0x" + Long.toHexString(CheckSum));
		logger.debug("  Subsystem = " + Subsystem);
		logger.debug("  DllCharacteristics = " + "0x" + Integer.toBinaryString(DllCharacteristics));
		logger.debug("  SizeOfStackReserve = " + SizeOfStackReserve);
		logger.debug("  SizeOfStackCommit = " + SizeOfStackCommit);
		logger.debug("  SizeOfHeapReserve = " + SizeOfHeapReserve);
		logger.debug("  SizeOfHeapCommit = " + SizeOfHeapCommit);
		logger.debug("  LoaderFlags = " + "0x" + Long.toBinaryString(LoaderFlags));
		logger.debug("  NumberOfRvaAndSizes = " + NumberOfRvaAndSizes);

		logger.debug("  DataDirectory[" + NumberOfRvaAndSizes + "] = \n  {");

		for (int i=0;i<NumberOfRvaAndSizes;i++){
			logger.debug("    {\n      VirtualAddress = " + "0x" + Long.toHexString(DataDirectory[i].VirtualAddress) + "\n      Size = " + DataDirectory[i].Size + "\n    }");
			if (i<16)
				logger.debug(ImageDataDirectory.STRINGS[i]);
		}
		logger.debug("  }\n}");
	}

	public long getAddressOfEntryPoint() {
		return AddressOfEntryPoint;
	}

	/**
	 * @return the imageBase
	 */
	public long getImageBase() {
		return ImageBase;
	}

	/**
	 * @return the dataDirectory
	 */
	public ImageDataDirectory[] getDataDirectory() {
		return DataDirectory;
	}
}
